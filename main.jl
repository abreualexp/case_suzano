# 

using XLSX
using DataFrames
using Dates

function read_data()
    #### Leitura da aba "HORIZONTE"
    sheet = "HORIZONTE"
    horizonte = DataFrame(XLSX.readtable(ws,sheet))
    
    global H = horizonte[end,1]
    global T = range(1,H)
    global T0 = range(0,H)
    global T_CL = [h for h=1:31 if typeof(horizonte[h,:CICLO_LENTO]) == String]

    #### Leitura da aba "FROTA"
    sheet = "FROTA"
    frota = sort(DataFrame(XLSX.readtable(ws,sheet)),[:TRANSPORTADOR])
    global n_transportador = length(unique(frota.TRANSPORTADOR))
    global K = range(1,n_transportador)
    dict_frota = Dict(zip(frota.TRANSPORTADOR,K))
    global K_min = frota.FROTA_MIN
    global K_max = frota.FROTA_MAX

    #### Leitura da aba "GRUA"
    sheet = "GRUA"
    grua = sort(DataFrame(XLSX.readtable(ws,sheet)),[:TRANSPORTADOR])
    global cap_grua = grua.QTD_GRUAS
    global por_min = grua.PORCENTAGEM_VEICULOS_MIN
    
    #### Leitura da aba "BD_UP"
    sheet = "BD_UP"
    up = sort(DataFrame(XLSX.readtable(ws,sheet)),[:UP])
    n_farm = length(unique(up.FAZENDA))
    F = range(1,n_farm)
    dict_farm = Dict(zip(unique(up.FAZENDA),F))
    n_up = length(unique(up.UP))
    global U = range(1,n_up)
    dict_up = Dict(zip(up.UP,U))
    insertcols!(up,:DATA_COLHEITA,:DIA_COLHEITA => day.(up.DATA_COLHEITA))
    global up_farm = zeros(Int,n_up)
    for l in 1:size(up)[1]
        up_farm[l] = dict_farm[up.FAZENDA[l]]
    end
    global up_db = up.DB
    global up_vol = up.VOLUME
    global up_rsp = up.RSP
    global up_dia = up.DIA_COLHEITA
    
    #### Leitura da aba "FABRICA"
    sheet = "FABRICA"
    fabrica = sort(DataFrame(XLSX.readtable(ws,sheet)),[:DIA])
    global demanda_min = fabrica.DEMANDA_MIN
    global demanda_max = fabrica.DEMANDA_MAX
    global rsp_min = fabrica.RSP_MIN
    global rsp_max = fabrica.RSP_MAX

    #### Leitura da aba "ROTA"
    sheet = "ROTA"
    rota = DataFrame(XLSX.readtable(ws,sheet))
    global carga = zeros(n_up,n_transportador)
    global tempo_ciclo = zeros(n_up,n_transportador)
    global tempo_ciclo_lento = zeros(n_up,n_transportador)
    global up_transp = zeros(n_up,n_transportador)
    for l in 1:size(rota)[1]
        u = dict_up[rota.ORIGEM[l]]
        r = dict_frota[rota.TRANSPORTADOR[l]]
        carga[u,r] = rota.CAIXA_CARGA[l]
        tempo_ciclo[u,r] = floor(rota.TEMPO_CICLO[l])
        tempo_ciclo_lento[u,r] = floor(rota.CICLO_LENTO[l])
        up_transp[u,r] = 1
    end

    println("\n## Leitura dos dados finalizada\n")
end

using JuMP
using Gurobi

function model()
    model = Model(Gurobi.Optimizer)
    
    # set_optimizer_attribute(model,"SolutionLimit", 2)
    # set_optimizer_attribute(model,"TimeLimit", 1500)
    
    @variables model begin
        Q[K,U,T]>=0
        v[K,U,T0]>=0
        G[K,U,T],Bin
        B[U,T0]>=0
        var_DB[T]>=0

        aux[U,T]>=0
    end
    
    ex_Q = 3

    @constraints model begin
        c01[r in K,t in T], sum(G[r,u,t] for u in U) <= cap_grua[r]
        c02[u in U,i in U,r in K,t in T;(up_farm[u]!=up_farm[i])], G[r,u,t] + G[r,i,t] <= 1
        c03[r in K,u in U,t in 2:H], G[r,u,t] >= B[u,t]/up_vol[u] - (1 - G[r,u,t-1])
        c04[r in K,u in U], sum(G[r,u,t] for t in T) <= H*up_transp[u,r]
        
        c05[r in K,t in T], sum(Q[r,u,t] for u in U) >= K_min[r]
        c06[r in K,t in T], sum(Q[r,u,t] for u in U) <= ex_Q*K_max[r]
        
        c07[r in K,u in U,t in T], Q[r,u,t] <= ex_Q*up_transp[u,r]*K_max[r]*G[r,u,t]
        c08[r in K,u in U,t in T], Q[r,u,t] >= por_min[r]*sum(Q[r,:,t]) - ex_Q*K_max[r]*(1 - G[r,u,t])
        
        c09[t in T], sum(v[r,u,t] for r in K for u in U) >= demanda_min[t]
        c10[t in T], sum(v[r,u,t] for r in K for u in U) <= demanda_max[t]
        
        c11[u in U,t in T0;(t<up_dia[u])], sum(v[r,u,t] for r in K) == 0
        c12[u in U], sum(v[r,u,t] for r in K for t in T) == up_vol[u]
        
        c13[r in K,u in U,t in T], v[r,u,t] <= Q[r,u,t]*tempo_ciclo[u,r]*carga[u,r]
        c14[r in K,u in U,t in T], v[r,u,t] <= up_vol[u]*G[r,u,t]
        c15[r in K,u in U,t in T], v[r,u,t] >= B[u,t]/up_vol[u] - up_vol[u]*(1 - G[r,u,t])
        
        c16[u in U,t in T], sum(v[r,u,t] for r in K) <= B[u,t]
        c17[u in U], B[u,H] == sum(v[r,u,H] for r in K)
        
        c17[u in U,t in T0;(t<up_dia[u])], B[u,t] == 0
        c19[u in U], B[u,up_dia[u]] == up_vol[u]
        c20[u in U,t in 2:H;(t>up_dia[u])], B[u,t] == B[u,t-1] - sum(v[r,u,t-1] for r in K)
        
        obj[i in U, u in U,t in T], var_DB[t] >= (up_db[i]*sum(G[r,i,t] for r in K) - up_db[u]*sum(G[r,u,t] for r in K))

        # c12b[t in T], sum((sum(v[r,u,t] for r in K)*up_rsp[u])/up_vol[u] for u in U) <= rsp_max[t]
        # c12a[t in T], sum((sum(v[r,u,t] for r in K)*up_rsp[u])/up_vol[u] for u in U) >= rsp_min[t]
    end

    # @NLconstraints model begin
    #     c12b[t in T], sum(sum(v[r,u,t] for r in K)*up_rsp[u] for u in U)/sum(v[r,u,t] for r in K for u in U) <= rsp_max[t]
    #     c12a[t in T], sum(sum(v[r,u,t] for r in K)*up_rsp[u] for u in U)/sum(v[r,u,t] for r in K for u in U) >= rsp_min[t]
    # end

    @objective(model, Min,
        sum(var_DB[t] for t in T)
    )

    optimize!(model)

    println("\n## Implementação do modelo finalizada\n")
    
    p_stt = primal_status(model)
    t_stt = termination_status(model)
    
    println(
        "Primal      : $p_stt\n",
        "Termination : $t_stt"
    )

    if (p_stt == MOI.NO_SOLUTION) || (t_stt == MOI.INFEASIBLE)
        return
    end

    global Q = value.(Q).data
    global G = value.(G).data
    global B = value.(B).data
    global v = value.(v).data
    global var_DB = value.(var_DB).data
    print()
end

function write_solution()

    for r in K, u in U, t in T
        if v[r,u,t] > 0
            out_file = open(out_ws,"a")
            out_text = DataFrame(
                UP = u,
                FAZENDA = up_farm[u],
                TRANSPORTADOR = r,
                DIA = t,
                DB = up_db[u],
                RSP = up_rsp[u],
                VEÍCULOS = Q[r,u,t],
                VOLUME = v[r,u,t]
            )
            CSV.write(out_file,out_text,append=true)
            close(out_file)
        end
    end
end

ws = "generic_input_case.xlsx"
out_ws = "solution.csv"

read_data()
# model()
# write_solution()