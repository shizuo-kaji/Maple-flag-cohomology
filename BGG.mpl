# # Comuting BGG operator and characteristic homomorphism
# # by Shizuo Kaji
# # version: 2007/12/10 12:30
# # See the included demo maple worksheet for usage
# # LIMITATION: due to computational complexity,
# #       for type-E this script deal with modulo
# #         maximal parabolic P2 by default

# require coxeter and weyl package by J.Stembridge
# http://www.math.lsa.umich.edu/~jrs/maple.html

# Data files
# E8data.m: load reduced words of E8 up to length 15, into a variable "redu"
# E8data-P2.m: load reduced words of E8/P2, into a variable "redu"
# E8gen.mpl: load definition for ring generators of E8/T

# global variables:
# R: Lie type
# B: simple roots
# redu[deg]: reduced words
# reduw: flattened list of reduced words
# w[i]: i-th weight
# a[i]: i-th root
# s[[]]: weyl group element
# X[weyl]: Schubert class corresponding to weyl
# S[weyl]: Schubert polynomial corresponding to weyl
# gam[deg],x[deg]: special generator
# rho[deg]: relation

with(coxeter); with(weyl);
with(WeylOps):

# convert poly of weights into that of e
w2e := proc (wpol::polynom) global R,B;
    return eval(wpol, [seq(w[j]=weights(R)[j], j=1..nops(B))]);
end proc;

# convert poly of special generators to that of weights "w[1..r]"
gen2w := proc (f::polynom) global R,B;
    return eval(f, [seq(G[i] = gam[i], i = [3,4,5,6,9,10,15]),
		seq(c[i] = c(i), i = 1 .. nops(B)),
		seq(T[i] = t[i], i = 0 .. 8)]);
end proc;

# listup monomials of degree "deg" consisting of "gens", whose degrees are specified by "degs"
list_monom := proc (gens::list, degs::list, deg::integer) local i, L;
 L := {};
 for i to nops(gens) do
   if 0 < deg-degs[i] then
     L := `union`(L, map2(`*`, gens[i], list_monom(gens, degs, deg-degs[i])))
   elif deg-degs[i] = 0 then
     L := `union`(L, {gens[i]});
   end if;
 end do;
 return L;
end proc:

# BGG operator for w-poly wrt any root
BGG_root := proc (vec::linear, f::polynom) global R;
    return -simplify((f - subs([seq(w[i]=e2w(reflect(vec, weights(R)[i])),i=1..rank(R))], f))
	      / e2w(vec));
end proc;

# BGG for w-poly by recursive computation using Leibniz-rule
BGG_w := proc (rt::integer, f::polynom) local i, j, term;
	if degree(f) < 1 then return 0
    elif type(f, monomial) then
		return -sum(ref_weight(rt)^i*w[rt]^(-i-1)*f, i=0..degree(f, w[rt])-1);
    elif op(0, f) = `+` then
		return expand(map2(procname, rt, f));
    elif op(0, f) = `*` then
		if type(op(1,f), 'rational') then
			return op(1,f)*procname(rt, f/op(1,f));
		end if;
		j := 1;
		for i to nops(f) do
		    if degree(op(i, f)) <= degree(op(j, f)) and length(op(i, f)) < length(op(j, f)) then
			j := i
		    end if
		end do;
		term[1] := op(j, f);
		term[2] := mul(op(i, f), i = 1 .. j-1)*mul(op(i, f), i = j+1 .. nops(f));
		return procname(rt, term[1])*term[2]+ref_rt(rt, term[1])*procname(rt, term[2]);
    elif op(0, f) = `^` then
	    term[1] := op(1, f);
	    return procname(rt, term[1])*add(term[1]^(i-1)*ref_rt(rt, term[1])^(op(2,f)-i),i=1..op(2,f));
    else
        print("cannot compute BGG:",f);
        return infinity;
    end if
end proc;

# BGG operator for e-poly
BGG_e := proc (rt::integer, f::polynom) global R;
    return -simplify((f - subs([seq(e(i)=reflect(B[rt], e(i)),i=1..dimr(R))], f))
	      / B[rt]);
end proc;

# a simple reflection on fundamental weight
ref_weight := proc (rt::integer) option remember; global R,B;
	return w[rt]-e2w(B[rt]);
end proc;

# simple reflection on Schubert cycle
ref_weyl := proc(rt::integer,weyl::list) local a,j,v,u,w,temp; global B; option remember;
	temp := X[weyl];
	w := weyl.[rt];
    if nops(w) > nops(weyl) then
		return X[weyl];
	end if;
	for a in pos_roots(B) do
       	 v := reflect(a,interior_pt(B));
     	 v := reflect(seq(B[j],j=w),v);
	  	  vec2fc(v,R,'u');    # u = w.s_a
		  if nops(u)=nops(weyl) then
			   temp := temp - iprod(2/iprod(a,a)*a,B[rt])*X[u];
          end if;
     end do;
     return temp;
end proc:

# simple reflection on polynomial
ref_rt := proc (rt::integer, f::polynom) local ff;
    if type(f, 'rational') then
        return f;
    else
        ff:=subs(w[rt]=ref_weight(rt), f);
        if has(f,'X') then
            if type(ff, 'indexed') and op(0,ff)='X' then return ref_weyl(rt,op(1,ff));
            elif op(0,ff) =`+` or op(0,ff)=`*` then return map2(procname, rt, ff);
            elif op(0,ff) =`^` then return procname(rt,op(1,ff))^op(2,ff);
            end if;
        end if;
        return ff;
    end if;
end proc;

# weyl group action on polynomial
ref := proc(weyl, f::polynom);
    return WeylFunc(weyl,f,ref_rt);
end proc:

# Schubert basis expansion
Char := proc (f::polynom, func::procedure, roots::set, R) local weyl;
    return add( WeylFunc(weyl, f, func)*X[weyl],
	       weyl=PReducedWd(R, roots, degree(f))[degree(f)]);
end proc;

# Schubert basis expansion for poly in special generators
Char_w := proc (f::polynom) local temp, deg; global redu; global R;
	temp:=collect(gen2w(f), {seq(w[i], i=1..rank(R))});
    if not type(temp, polynom) then
        print('not polynomial', f); return -infinity;
    end if;
    deg := degree(temp);
    if deg < 1 then return temp;
	elif deg <> ldegree(temp) then
		print("not homogeneous:", temp); return -infinity;
    elif deg>nops(redu) then return 0;
    end if;
	return add(WeylFunc(weyl, temp, BGG_w)*X[weyl], weyl=redu[deg]);
# for multi thread
#	return Threads:-Add( WeylFunc(weyl, temp)*X[weyl], weyl=redu[deg] );
end proc;

# Schubert basis expansion for poly in "X[weyl]"
Char_X := proc(f::polynom) local weyl,deg; global redu;
    deg := deg_X(f);
    if deg < 1 then return f;
    elif deg>nops(redu) then return 0;
    end if;
  return add(WeylFunc(weyl, f, BGG_X)*X[weyl], weyl=redu[deg]);
end proc:

# Schubert basis expansion for poly in "e"
Char_e := proc(f::polynom) local weyl,deg; global redu;
    deg := degree(f);
    if deg <1 then return f;
	elif deg <> ldegree(f) then
		print("not homogeneous:", f); return -infinity;
    elif deg>nops(redu) then return 0;
    end if;
  return add(WeylFunc(weyl, f, BGG_e)*X[weyl], weyl=redu[degree(f)]);
end proc:

# BGG operator for poly in "X[weyl]"
BGG_X := proc(rt::integer, f::polynom) local w,term;
    if degree(f) < 1 then return 0 end if;
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
	    return expand(procname(rt, term[1])*add(term[1]^(i-1)*ref_rt(rt, term[1])^(op(2,f)-i),i=1..op(2,f)));
    else
	    print("Error in BGG_X:",f)
    end if;
end proc;


# top (point) cohomology class
top := proc (roots::set := {}) local k, j, i, RP, temp, lie_type; global R,P,reduw;
	if not roots={} then
       RP := relative_roots(R,roots);
	   return (-1)^(nops(RP))*mul(i,i=RP)/nops(reduw);
    end if;
    temp := 1;
	lie_type := name_of(R);
    if lie_type = F4 then
        return (-255887*gam[3]^4*gam[4]^3+178123*gam[4]^6)/173408256000;
    elif lie_type = E7 then
		temp := mul(t[i]-t[0], i = 1 .. 7);
		for i to 6 do temp := temp*mul(t[i]-t[j], j = i+1 .. 7) end do;
	    for i to 5 do
		 for j from i+1 to 6 do
			temp := temp*mul(t[i]+t[j]+t[k]-t[0], k = j+1 .. 7);
	     end do;
		end do;
		return temp;
    elif lie_type = E8 then
		temp := mul(t[i], i = 1 .. 8);
		for i to 7 do temp := temp*mul(t[i]-t[j], j = i+1 .. 8) end do;
		for i to 7 do temp := temp*mul(t[i]+t[j]-t[0], j = i+1 .. 8) end do;
		for i to 6 do
			for j from i+1 to 7 do
				temp := temp*mul(t[i]+t[j]+t[k]-t[0], k = j+1 .. 8)
			end do;
		end do;
		return temp;
    elif lie_type = G2 then
		return (-9*w[1]^6+6*w[1]^5*w[2])/12;
    elif lie_type = cat('A',rank(R)) then
	     return mul(e(i)^(rank(R)-i+1), i = 1 .. rank(R));
	elif lie_type = cat('B',rank(R)) then
		 return (-1)^rank(R)*mul(e(i)^(2*i-1), i = 1 .. rank(R))/2^rank(R);
    elif lie_type = cat('C',rank(R)) then
		 return (-1)^rank(R)*mul(e(i)^(2*i-1), i = 1 .. rank(R));
    else
		return (-1)^(nops(P))*mul(i, i = P)/mul(i,i=degrees(R));
    end if
end proc;

# enumerate Schubert polynomials by applying BGG to the top degree class
schubertpolys := proc() global S, R, reduw; local w,func,top_class,top_weyl;
  top_class := top();
  top_weyl  := longest_elt(R);
  S[[]] := 1;
  if evalb(name_of(R) in {'G2','F4','E6','E7','E8'}) then
  	 func:='BGG_w';
  else
	func:='BGG_e';
  end if;
  for w in reduw do
  	   S[w] := WeylFunc(inv(w).top_weyl, top_class, func);
  end do;
  print("The top class is", top_weyl, top_class);
end proc:

# polynomial representatives in given generators for Schubert classes in a given degree
Schubert_Polynomials := proc (gens::list, deg::integer) local i,j,v,temp,M,L,A,V,degs;
 L:=[]; A:=[];
 degs := map(degree, map(gen2w, gens));
 M := convert(list_monom(gens, degs, deg), `list`);
 for i from 1 to nops(M) do
  temp := Char_w(M[i]);
  L:=[op(L), M[i] = temp];
  v := vector(nops(redu[deg])+nops(M), 0);
  v[nops(redu[deg])+i] := 1;
  for j to nops(redu[deg]) do
     v[j] := coeff(temp, X[redu[deg][j]]);
  end do;
  A := [op(A), convert(v, list)];
 end do;
 A := LinearAlgebra[HermiteForm](Matrix(A));
# for printing
 V := [];
 for v in convert(A, `listlist`) do
	V := [op(V),
	    add(v[i]*X[redu[deg][i]], i=1..nops(redu[deg]))
        = add(v[nops(redu[deg])+i]*M[i], i=1..nops(M))];
  end do;
  return V;
end proc:



## initialization for Lie types (using Toda-Watanabe basis for exceptional types)
setup := proc (lie_type, roots::set := {}, upto::integer := 0) local i,S;
		global R, P, B, x, u, z, t, udim, gam, rho, redu, reduw;
  forget(ref_weight);
  forget(ref_weyl);
  unassign('gam','t','x','S','rho');

# type G2
  if lie_type = G2 then
    R := lie_type;
    t[1] := -w[1];
    t[2] := -w[1]+w[2];
    t[3] := 2*w[1]-w[2];
    rho[2] := w[2]^2+3*w[1]^2-3*w[1]*w[2];
    gam[3] := (1/2)*t[1]*t[2]*t[3];
	x[3] := 1/2*(w[1]*w[2]^2-w[1]^2*w[2]); # [2,1,2]
# type F4
  elif lie_type = F4 then
    R := linalg[transpose](cartan_matrix(lie_type));
    t[1] := -w[4];
    t[2] := w[1]-w[4];
    t[3] := -w[1]+w[2]-w[4];
    t[4] := -w[2]+2*w[3]-w[4];
    t[0] := w[3]-2*w[4];
    gam[3] := (1/2)*c(3);
    gam[4] := (1/3)*c(4)-(2/3)*t[0]*c(3)+(8/3)*t[0]^4;
	rho[2] := c(2)-2*t[0]^2;
	rho[6] := gam[3]^2-3*t[0]^2*gam[4]-4*t[0]^3*gam[3]+8*t[0]^6;
	rho[8] := 3*gam[4]^2+6*t[0]*gam[3]*gam[4]-3*t[0]^4*gam[4]-13*t[0]^8;
# type E6 / P2
  elif lie_type = E6 then
    R := linalg[transpose](cartan_matrix(lie_type));
    t[1] := -w[1]+w[2];
    t[2] := w[1]+w[2]-w[3];
    t[3] := w[2]+w[3]-w[4];
    t[4] := w[4]-w[5];
    t[5] := w[5]-w[6];
    t[6] := w[6]; t[0] := w[2];
    gam[3] := c(3);
    gam[4] := c(4)+2*t[0]^4;
# type E7 / P2
  elif lie_type = E7 then
    R := linalg[transpose](cartan_matrix(lie_type));
    t[1] := -w[1]+w[2];
    t[2] := w[1]+w[2]-w[3];
    t[3] := w[2]+w[3]-w[4];
    t[4] := w[4]-w[5];
    t[5] := w[5]-w[6];
    t[6] := w[6]-w[7];
    t[7] := w[7];
    t[0] := w[2];
    gam[3] := 1/2*c(3);
    gam[4] := 1/3*(c(4)+2*t[0]^4);
    gam[5] := 1/2*(c(5)-t[0]*c(4)+t[0]^2*c(3)-2*t[0]^5);
    gam[9] := 1/2*(c(6)*c(3)+t[0]^2*c(7)-3*t[0]^3*c(6));
# type E8 / P2
  elif lie_type = E8 then
    R := linalg[transpose](cartan_matrix(lie_type));
	read "E8data-p2.m";
	read "E8gen.mpl";
  else
    R := lie_type;
  end if;

  B := base(R);
  P := pos_roots(lie_type);
  udim := `if`(upto>0,upto,nops(P));
  if not lie_type = E8 then
      redu := PReducedWd(R, roots, udim);
  end if;
  reduw := [[],seq(op(i),i=redu)];
  print(lie_type, "mod the parabolic w.r.t", roots);
  return diagram(R);
end proc;
