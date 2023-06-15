def atMostN(X, n):
        # Output CNF clauses that ensure that no more than n of 
        # the literals in (the list) X are true
        # See Knuth: formulas (18) and (19)
        result = []
        S = [sat.newVars(len(X) - n) for k in range(n)]
        for j in range(0, len(X)-n):
            result.append([-X[j], S[0][j]])
            for k in range(0, n):
                if k < n-1:
                    if j < len(X) - n - 1:
                        result.append([-S[k][j], S[k][j+1]])
                    result.append([-X[j+k+1], -S[k][j], S[k+1][j]]) 
                else:
                    if j < len(X) - n - 1:
                        result.append([-S[k][j], S[k][j+1]]) 
                    result.append([-X[j+k+1], -S[k][j]]) 
        return result
