# # Computation for the equivariant cohomology of G/B
# # by Shizuo Kaji

# it requires coxeter and weyl package by J.Stembridge
# http://www.math.lsa.umich.edu/~jrs/maple.html

# symbols
# e(i), a[i]: elements in H^*(BT) in abstract coordinate and root coordinate
# x[i], z[i]: elements in H^*(G/T) in abstract coordinate and root coordinate

# look at the demo worksheet "BGGT_example.mw" for the details.

with(coxeter); with(weyl);with(WeylOps);

# decompose a word into products of smaller words
# used in "double"
decomp := proc(weyl::list) local L, i, temp;
 if nops(weyl)=1 then return {[weyl]}; end if;
 temp:={};
 for i in descent(weyl) do
   for L in procname(weyl.[i]) do
     if nops(L)=1 then
	   temp:={op(temp), [op(L),[i]], [L[1].[i]]};
     else
       temp:={op(temp), [op(L),[i]], [op(1..-2,L),L[-1].[i]]};
     end if;
   end do;
 end do;
 return temp;
end proc:

# Enumerate subwords of "longweyl" which is equal to "weyl"
subwords := proc(weyl::list, longweyl::list) local i,L,W; global R;
  W := {};
  for L in combinat[choose]([seq(i,i=1..nops(longweyl))],nops(weyl)) do
    if reduce([seq(longweyl[i],i=L)], R)=weyl then
	   W:=W union {L};
    end if;
  end do;
  return W;
end proc;

## Utility Functions
# convert between e-poly and z-poly
e2x := proc(f::polynom);
	return eval(f,[seq(e(j)=x[j], j = 1 .. dimr(R))]);
end proc:
x2e := proc(f::polynom);
	return eval(f,[seq(x[j]=e(j) , j = 1 .. dimr(R))]);
end proc:
e2u := proc(f::polynom);
	return eval(f,[seq(e(j)=u[j], j = 1 .. dimr(R))]);
end proc:

# convert between a-poly and z-poly
a2z := proc(f::polynom);
	return eval(f,[seq(a[j]=z[j], j = 1 .. rank(R))]);
end proc:

# BGG operator on GKM poly
BGG_GKM := proc(rt::integer, f::list(polynom), LR::symbol := 'R') local j,k,ff,v,u; global reduw, R, B, optype; option remember;
  ff := [seq(0,j=1..nops(reduw))];
  if LR='R' then
	for j from 1 to nops(reduw) do
		u := reflect(seq(B[reduw[j][k]],k=1..nops(reduw[j])),B[rt]);
		member(reduw[j].[rt],reduw,'v');
        if optype = 'e' then
            ff[j] := -simplify((f[j] - f[v])/u);
        else
            ff[j] := -simplify((f[j] - f[v])/e2a(u));
        end if;
	end do;
  elif LR='L' then
	for j from 1 to nops(reduw) do
		member([rt].reduw[j], reduw,'v');
        if optype = 'e' then
            ff[j]:=simplify((f[j]-subs({seq(e(i)=reflect(B[rt],e(i))
                                            ,i=1..dimr(R))},f[v]))/B[rt]);
        else
            ff[j]:=simplify((f[j]-subs({seq(a[i]=e2a(reflect(B[rt],B[i]))
                                            ,i=1..nops(B))},f[v]))/a[rt]);
        end if;
	end do;
  end if;
  return ff;
end proc:

# BGG on double polynomials
BGGT_e := proc(rt::integer, f::polynom, LR::symbol := 'R')
  if LR='R' then
    return -simplify((f - act([rt], f))/e2x(B[rt]));
  else
    return simplify((f - act([rt], f, 'L'))/B[rt]);
  end if;
  return -infinity;
end proc;
#
BGGT_a := proc(rt::integer, f::polynom, LR::symbol := 'R')
  if LR='R' then
      return -simplify((f - act([rt], f))/z[rt]);
  else
      return simplify((f - act([rt], f, 'L'))/a[rt]);
  end if;
  return -infinity;
end proc;

# BGG operator for poly in "X[weyl]"
BGGT_X := proc(rt::integer, f::polynom, LR::symbol := 'R') local ff,w,term;
    if degree(f) < 1 then
        return 0;
    elif LR = 'L' then
        if optype = 'e' then
            return (f-act([rt],f,'L'))/B[rt];
        else
            return (f-act([rt],f,'L'))/a[rt];
        end if;
    elif LR ='R' then
        if type(f, 'indexed') and op(0,f)=`X` then
            w:=op(1,f).[rt];
            if nops(w)=0 then return 1;
            elif nops(w) < nops(op(1,f)) then return(X[w]);
            else return 0;
            end if;
        elif op(0, f) = `+` then
            return expand(map2(procname, rt, f));
        elif op(0, f) = `*` then
            if type(op(1,f), 'rational') then
                return op(1,f)*procname(rt, f/op(1,f));
            end if;
            term[1] := op(1, f);
            term[2] := mul(op(i, f), i = 2 .. nops(f));
            return expand(procname(rt, term[1])*term[2]
                          +ref_rt(rt, term[1])*procname(rt, term[2]));
        elif op(0, f) = `^` then
            term[1] := op(1, f);
            return expand(procname(rt, term[1])*add(term[1]^(i-1)*act([rt], term[1])^(op(2,f)-i),i=1..op(2,f)));
        end if;
        print("error in BGGT_X:",f);
    end if;
end proc;

# BGG operator for weyl words
BGGweylT := proc(weyl::list, f::{list(polynom),polynom}, LR::symbol := 'R')
                 global optype; local i,temp,func;
	temp := f;
	if type(f, list(polynom)) then
	   func := 'BGG_GKM';
    elif has(f,`X`) then
        func := 'BGGT_X';
    elif type(f, polynom) then
	   func := cat('BGGT_',optype);
    else
        print("error in BGGWeylT:",f);
        return -infinity;
    end if;
	for i from nops(weyl) to 1 by -1 do
		temp := func(weyl[i], temp, LR);
	end do;
	return temp;
end proc:


# Weyl group action on polynomials
act := proc(weyl::list, f::ratpoly, LR::symbol := 'R') local ff,t,rt; global R,optype;
    if nops(weyl)=0 then
        return f;
    elif nops(weyl)>1 then
        return procname(weyl[1..-2],procname([weyl[-1]],f,LR),LR);
    elif nops(weyl)=1 then
        rt := weyl[-1];
        if LR='R' then
            ff:=eval(f, [seq(x[i] = subs([seq(e(j) = x[j], j = 1 .. dimr(R))],
                               reflect(B[rt], e(i))), i = 1 .. dimr(R))]);
            ff:=eval(ff, [seq(z[i] = add(root_coords(reflect(B[rt],B[i]),R)[j]*z[j],
                                               j = 1 .. rank(R)), i = 1 .. rank(R))]);
            return eval(ff,[seq(t=ref_weyl(rt,op(1,t),'R'), t=indetsX(ff))]);
       elif LR='L' then
            ff:= eval(f, [seq(e(i)=reflect(B[rt], e(i)),
                              i = 1 .. dimr(R))]);
            ff := eval(ff, [seq(a[i] = add(root_coords(reflect(B[rt], B[i]),R)[j]*a[j],
                                            j = 1 .. rank(R)), i = 1 .. rank(R))]);
            return eval(ff,[seq(t=ref_weyl(rt,op(1,t),'L'), t=indetsX(ff))]);
        end if;
    end if;
    print("error in act:",weyl,f);
    return -infinity;
end proc;

# enumerate X in a polynomial
indetsX := proc(f) local t,V;
    V:=[];
    for t in indets(f) do
        if type(t,'indexed') and op(0,t)=`X` then
            V:=[op(V),t];
        end if;
    end do;
    return V;
end proc:

# Weyl group action on X
ref_weyl := proc(rt::integer,weyl::list, LR::symbol := 'R') local b,j,v,u,w,temp; global B;
    if LR = 'R' then
        w := weyl.[rt];
        if nops(w) > nops(weyl) then
            return X[weyl];
        end if;
        temp := X[weyl]+act(w,B[rt],'L')*X[w];
        for b in pos_roots(B) do
            v := reflect(b,interior_pt(B));
            v := reflect(seq(B[j],j=w),v);
            vec2fc(v,R,'u');    # u = w.s_b
            if nops(u)=nops(weyl) then
                temp := temp - iprod(2/iprod(b,b)*b,B[rt])*X[u];
            end if;
        end do;
        return temp;
    elif LR = 'L' then
        w := [rt].weyl;
        if nops(w) > nops(weyl) then
            return X[weyl]
        else
            return -B[rt]*X[w]+X[weyl];
        end if;
    end if;
    print("error in ref_weyl:",rt,weyl);
    return -infinity;
end proc:

# evaluate poly at "w" by putting x[i]=w^{-1}e[i]
ev := proc(weyl::list, f::polynom) local ff; global R,optype;
      ff := eval(act(weyl,f), [seq(x[i] = e(i), i = 1 .. dimr(R))]);
      return eval(ff, [seq(z[i] = a[i], i = 1 .. rank(R))]);
end proc:

# orbit sum
orbit_sum := proc(f::polynom) global reduw,R;
  return expand(add(ev(weyl,f), weyl=reduw)/size(R));
end proc:

# push-forward in cohomology
push := proc(f::polynom) local d,weyl; global reduw,R,P;
    d := mul(e2x(i), i = P);
    return expand(ev([],(-1)^(nops(P))*simplify(add(act(weyl,f/d), weyl=reduw)))):
end proc:


# convert double polynomials to Schubert basis
P2X := proc(f::polynom) local weyl, temp, i; global R, redu;
    temp := ev([],f);
    for i to min(degree(f),nops(redu)) do
      temp := temp+add(
    	  ev([],BGGweylT(weyl, f))*X[weyl], weyl=redu[i]);
    end do;
	return col(temp);
end proc:

# Convert GKM polynomials to Schubert basis using upper triangularity
GKM2X := proc (f::list(polynom)) local i, j, it, lc, ff; global reduw;
   for it to nops(f) do
     if f[it] <> 0 then break; end if;
   end do;
   if nops(f) < it then return 0; end if;
   lc := normal(f[it]/GKM(reduw[it])[it]);
   ff := normal(zip(`-`, f, zip(`*`, lc, GKM(reduw[it]))));
   return col(lc*X[reduw[it]]+procname(ff));
end proc;

# Convert GKM polynomials to Schubert basis using right BGG operators
GKM2X2 := proc (f::list(polynom)) local i, deg, temp, weyl; global reduw;
    temp := f[1];
    deg := max(map(degree,f));
    for i to min(deg,nops(redu)) do
        temp := temp+add(BGGweylT(weyl, f)[1]*X[weyl], weyl=redu[i]);
    end do;
    return col(temp);
end proc;

# convert poly in "X" to Schubert basis
X2X := proc(f::polynom);
	return GKM2X(X2GKM(f));
end proc:

# Convert poly in "X" into GKM-poly
X2GKM := proc (f::polynom) local i, weyl; global reduw;
    return [seq(eval(f, [seq(X[weyl] = GKM(weyl)[i], weyl = reduw)]),i=1..nops(reduw))] ;
end proc;

# convert double poly into GKM-poly
P2GKM := proc(f::polynom);
    return ([seq(simplify(ev(w, f)), w = reduw)])
end proc:

# GKM polys (Billey's formula)
GKM :=proc(weyl::list, upto:=-1) option remember; global reduw;
 return [seq(GKM_internal(weyl,v),v=reduw[1..upto])];
end proc:

GKM_internal := proc(weyl::list, longweyl::list) local i,j,k,u,L,K,M; global R,B,optype;
  K := 0;
  for L in subwords(weyl, longweyl) do
    M := 1;
    for i from 1 to nops(weyl) do
      u := reflect(seq(B[longweyl[j]],j=1..L[i]-1), B[longweyl[L[i]]]);
	  if optype = 'e' then
	  	  M := M * u;
	  else
		  M := M * e2a(u);
	  end if;
	end do;
    K := K + M;
  end do;
  return simplify(K);
end proc:

# initialize for Lie type
setupT := proc (lie_type, roots::set :={}, upto::integer := 0) local i;
     global R, B, P, S, ST, redu, udim, reduw, optype, optypeK, w0;
  forget(GKM);
  forget(BGG_GKM);
  forget(refK); forget(strong_bruhat);
  unassign('S','ST');

  R := lie_type;
  B := base(R);
  P := pos_roots(R);
    optype := 'e';
    if R = cat('A',rank(R)) then
        optypeK := 'x'
    else
        optypeK := 'u'
    end if;
  udim := `if`(upto>0,upto,nops(P));
  redu := PReducedWd(R, roots, udim);
  reduw := [[],seq(op(i),i=redu)];
  w0 := longest_elt(R);
  return R;
end proc;

# TopSchubert poly
top := proc () local k, j, i, temp; global R,P;
   temp := 1;
   if optype='e' then
	if R = G2 then
	    return (-3*e2x(w[1])^6+2*e2x(w[1])^5*e2x(w[2]))/6;
    elif R = cat('A',rank(R)) then
	     return mul(x[i]^(rank(R)-i+1), i = 1 .. rank(R));
	elif R = cat('B',rank(R)) then
    	return mul(x[i]^(rank(R)-i), i = 1 .. rank(R))*mul(c(i,`x`)/2, i = 1 .. rank(R));
    elif lie_type = cat('C',rank(R)) then
		 return mul(x[i]^(2*rank(R)-2*i+1), i = 1 .. rank(R));
    elif R = E7 then
		temp := mul(x[i]-c(1,`x`), i = 1 .. 7);
		for i to 6 do temp := temp*mul(x[i]-x[j], j = i+1 .. 7) end do;
	    for i to 5 do
		 for j from i+1 to 6 do
			temp := temp*mul(x[i]+x[j]+x[k]-c(1,`x`), k = j+1 .. 7);
	     end do;
		end do;
		return temp;
    elif R = E8 then
		temp := mul(t[i], i = 1 .. 8);
		for i to 7 do temp := temp*mul(t[i]-t[j], j = i+1 .. 8) end do;
		for i to 7 do temp := temp*mul(t[i]+t[j]-t[0], j = i+1 .. 8) end do;
		for i to 6 do
			for j from i+1 to 7 do
				temp := temp*mul(t[i]+t[j]+t[k]-t[0], k = j+1 .. 8)
			end do;
		end do;
		return temp;
    else
		return mul(e2x(i), i = P)/mul(i, i=degrees(R));
    end if;
   else
	if R = G2 then
   		return z[1]^5*z[2]/2;
	else
		return mul(a2z(-e2a(i)), i = P)/mul(i, i=degrees(R));
    end if;
   end if;
end proc;

# Top double poly
topT := proc() global R,optype,S,w0;  local u, i, j, k, D, temp;
  if optype='e' then
     if R = cat('A',rank(R)) then
	     return mul(mul(x[i]-e(j), j = 1 .. rank(R)-i+1), i = 1 .. rank(R)+1);
	 elif R = cat('B',rank(R)) then
	    #  D:=Matrix(rank(R));
		#  for i from 1 to rank(R) do
		#     for j from 1 to rank(R) do
		#          k:=rank(R)+1+j-2*i;
		# 		 if k<=rank(R) and k>=0 then
		# 		   D[i,j]:=(c(k,`x`)+eval(c(k,`t`),[seq(t[h]=e(h),h=1..rank(R))]))/2;
		# 		 end if;
		# 	end do;
		# end do;
		# return act(longest_elt(R),mul(mul(x[i]-e(j), j = 1 .. i-1), i = 2 .. rank(R))
		#   *LinearAlgebra[Determinant](D));
   return  mul(mul(x[i]-e(j), j = 1 .. i), i = 1 .. rank(R))
                  *mul(mul(x[i]+e(j), j = 1 .. i-1), i = 1 .. rank(R))/(-2)^rank(R);

	 elif R = cat('C',rank(R)) then
	    #  D:=Matrix(rank(R));
		#  for i from 1 to rank(R) do
		#     for j from 1 to rank(R) do
		#          k:=rank(R)+1+j-2*i;
		# 		 if k<=rank(R) and k>=0 then
		# 		   D[i,j]:=(c(k,`x`)+eval(c(k,`t`),[seq(t[h]=e(h),h=1..rank(R))]));
		# 		 end if;
		# 	end do;
		# end do;
		# return act(longest_elt(R),mul(mul(x[i]-e(j), j = 1 .. i-1), i = 2 .. rank(R))
		#   *LinearAlgebra[Determinant](D));
        return   mul(mul(x[i]-e(j), j = 1 .. i), i = 1 .. rank(R))
                  *mul(mul(x[i]+e(j), j = 1 .. i-1), i = 1 .. rank(R));
	 elif R = cat('D',rank(R)) then
	     D:=Matrix(rank(R));
		 for i from 1 to rank(R) do
		    for j from 1 to rank(R) do
		         k:=rank(R)+j-2*i;
				 if k<=rank(R) and k>=0 then
				     D[i,j]:=(c(k,`x`)+eval(c(k,`t`),[seq(t[h]=e(h),h=1..rank(R))]))/2;
				 end if;
			end do;
		end do;
		return act(w0,mul(mul(x[i]-e(j), j = 1 .. i-1), i = 2 .. rank(R))
                   *LinearAlgebra[Determinant](D));
     elif R = G2 then
         return ((x[1]-x[2]+e2-e1)/2)*(x[2]-x[1]-e2+e3)*(x[2]-x[1]-e1+e3)
         *(x[1]-x[2]-e2+e3)*(x[1]-x[2]-e1+e3)*(-x[1]+2*x[2]-x[3]+e2-2*e1+e3);
#	     return -(x[3]-(2/3)*e3+(1/3)*e1-(2/3)*e2)*((3/2)*x[1]-(3/2)*e1)*(3*x[1]-3*e2)
#         *(3*x[1]-3*e3)*(x[2]-(2/3)*e1-(2/3)*e2+(1/3)*e3)*(x[2]-(2/3)*e3+(1/3)*e1-(2/3)*e2);
	 elif type(name_of(R),'indexed') then       # type I2
	      D:=[]; temp:=x[2]-e2;
	      for i from 1 to trunc(op(1,name_of(R))/2-1) do
		     D:=[1,2,op(D)];
		     temp:=temp*(x[2]-act(D,e2,'L'));
		  end do;
		  D:=[];
		  for i from 1 to trunc((op(1,name_of(R))-1)/2) do
		     D:=[2,1,op(D)];
		     temp:=temp*(x[2]-act(D,e2,'L'));
		  end do;
	      return temp*(x[1]+act(w0,e1,'L'));
	 else
	    return double(w0);
	 end if;
  elif optype='a' then
     if R = G2 then
         return ((-z[1]+a[1])/2)*(z[1]+a[1]+a[2])*(z[1]+2*a[1]+a[2])
         *(-z[1]+a[1]+a[2])*(-z[1]+2*a[1]+a[2])*(-z[2]+3*a[1]+a[2]);
     elif R = cat('A',rank(R)) then
        for i from 1 to rank(R)+1 do
	       u[i] := e2a(-add(e(j), j = 1 .. rank(R)+1)/(rank(R)+1) + e(i));
	    end do;
        return mul(mul(eval(u[i],[seq(a[k]=z[k],k=1..rank(R))])-u[j], j = 1 .. rank(R)-i+1),
	        i = 1 .. rank(R)+1);
     else
	    return double(w0);
	 end if;
  end if:
end proc:


# enumerate Schubert polynomials
schubertpolys := proc () global S,reduw,w0; local w,f;
  f:=top();
  for w in reduw do
	 S[w] := simplify(BGGweylT(inv(w).w0,f));
  end do;
  print("The top schubert poly is",f);
end proc:

# enumerate Double Schubert polynomials
schubertpolysT := proc () global optype,ST,reduw,w0; local w,f;
  f:=topT();
  for w in reduw do
	 ST[w] := simplify(BGGweylT(inv(w).w0,f));
  end do;
  print("The top double schubert poly is",f);
end proc:

# single to double formula
# compute double Schubert poly "ST[weyl]" from single Schubert polys "S[]"
double:=proc(weyl::list) global S; local temp,L;
  if optype = 'e' then
      return add((-1)^(nops(L))*mul(x2e(S[L[i]]),i=1..nops(L)-1)
                 *(x2e(S[L[-1]])-S[L[-1]]),L=decomp(weyl));
  else
      return add((-1)^(nops(L))*mul(z2a(S[L[i]]),i=1..nops(L)-1)
                 *(z2a(S[L[-1]])-S[L[-1]]),L=decomp(weyl));
  end if;
end proc:

# double to single
single:=proc(f::polynom) local ff; global R;
    ff := eval(f,[seq(e(j) = 0, j = 1 .. dimr(R))]);
    return eval(ff, [seq(a[j] = 0, j = 1 .. rank(R))]);
end proc:

# Cauchy formula for type A
Cauchy:=proc() global reduw,w0 ;local weyl;
 return add((-1)^(nops(weyl))*x2e(S[weyl])*S[weyl.w0],weyl=reduw);
end proc:

# Chevalley formula computes "X[weyl]X[rt]"
Chev := proc(weyl::list,rt::integer) local j,v,u,temp; global w,P;
	 temp := 0;
     for v in P do
       	 vec2fc(reflect(seq(B[j], j = weyl),v,interior_pt(R)),R,'u');
         if nops(u)=nops(weyl)+1 then
		   temp := temp + iprod(2/iprod(v,v)*v,w[rt])*X[u];
         end if;
     end do;
     return (w[rt]-reflect(seq(B[j], j = weyl),w[rt]))*X[weyl]+temp;
end proc:

# collect terms in Schubert presentation
col := proc(f::algebraic) local g; global reduw;
    g := collect(simplify(f),[seq(X[weyl],weyl=reduw)]);
    return collect(g,[seq(XK[weyl],weyl=reduw)]);
end proc:

