# # Weyl group related operations on weyl word
# #       by Shizuo Kaji
# requires coxeter and weyl package by J.Stembridge
# http://www.math.lsa.umich.edu/~jrs/maple.html
#
# global variables:
# R: Lie type
# B: the set of simple roots

WeylOps := module() option package;
  export `.`,inv,descent,minrep,PReducedWd,WeylFunc,e,c,symmetric,e2w,e2a,a2e,a2w,w2a,deg_X,dimr,relative_roots,e2ref,action,oneline;
  # inverse of weyl word
  inv := proc (weyl::list);
	return ListTools[Reverse](weyl);
  end proc;

  # operator '.' as product
  `.` := overload(
  [
    proc(a::list, b::list) option overload(callseq_only); global R;
       return(reduce([op(a),op(b)],R));
    end,
    proc(a::indexed, b::indexed) option overload(callseq_only);
        if op(0,a)=`s` and op(0,b)=`s` then
            return(s[op(1,a).op(1,b)]);
        else
            return(a*b);
        end if;
    end,
    proc(a::`+`, b::anything)  option overload(callseq_only);
        return map(`.`,a,b);
    end,
    proc(a::anything, b::`+`)  option overload(callseq_only);
        return map2(`.`,a,b);
    end,
    proc(a::`*`, b::anything)  option overload(callseq_only);
        return op(1,a)*((a/op(1,a)).b);
    end,
    proc(a::anything, b::`*`)  option overload(callseq_only);
        return op(1,b)*(a.(b/op(1,b)));
    end
  ]
):

# descent set of the weyl word "weyl"
descent := proc(weyl::list) local i, V; global R;
	V := {};
	for i from 1 to rank(R) do
	   if nops(weyl.[i]) < nops(weyl) then
    		V := {op(V), i};
	   end if;
    end do:
	return V;
end proc;

# minimal coset representative of "weyl" according to "roots"
minrep := proc(weyl::list, roots::set) local i,temp; global R;
  for i in roots do
      temp:=weyl.[i]:
      if nops(temp) < nops(weyl) then return(procname(temp, roots)); end if:
  end do:
  return(weyl):
end proc:

# enumerate all reduced words (minimal coset representatives) of "R" upto length "len"
PReducedWd := proc (R, roots::set:={}, maxlen::integer:=nops(longest_elt(R)))
  local B, r, v, i, j, len, newvects, newwords, words, oldvects;
    B := base(R); r := rank(B);
	newvects := [add(weights(R)[i], i={$1..r} minus roots)];
    words := Array(0..maxlen); words[0]:=[[]];
    for len from 1 to maxlen do;
        oldvects := newvects;
        newvects := []; newwords := NULL;
        for j to nops(oldvects) do
            for i to r do
                if 0 < iprod(B[i], oldvects[j]) then
                    v := reflect(B[i], oldvects[j]);
                    if not member(v, newvects) then
                        newvects := [op(newvects), v];
                        newwords := newwords, reduce([i,op(words[len-1][j])],R);
                    end if
                end if
            end do
        end do;
        words[len] := [newwords];
        if newwords=NULL then break; end if;
    end do;
    return convert(words[1..ArrayNumElems(words)-1],list);
end proc;

# iterative application of a function of simple roots for a weyl word poly
WeylFunc := proc(weyl, f::polynom, func::procedure) local i,temp;
	temp := f;
    if type(weyl,'numeric') then
        return weyl*f;
    elif type(weyl,'list') then
        for i from nops(weyl) to 1 by -1 do
            temp := func(weyl[i], temp);
        end do;
        return temp;
    elif type(weyl, 'indexed') then
        if op(0,weyl)=`s` then
            return procname(op(1,weyl), f, func);
        else
            return weyl*f;
        end if;
    elif type(weyl, linear) then
	  return add(coeff(weyl,ind)*procname(ind, f, func), ind=indets(weyl));
    else
        print("error in WeylFunc:",weyl);
    end if;
end proc:

## Utility Functions
# coordinate variables
e := proc (j::integer);
    return cat('e', j);
end proc;

# elementary symmetric function "c(i)" of "t[1..r]"
c := proc (deg::integer,sym::symbol := `t`) global R;
    return symmetric(deg, [seq(sym[i], i = 1 .. rank(R))])
end proc;

# elementary symmetric function of degree "deg" in "vars"
symmetric := proc (deg::integer, vars::list) local T;
    return sort(expand(coeff(mul(T+i, i=vars), T, nops(vars)-deg)));
end proc;

# convert vector in "e" into weights "w[1..r]"
e2w := proc (el::linear) global R;
    return add(weight_coords(el, R)[i]*w[i], i=1..rank(R));
end proc;

# convert vector in "e" into simple roots "a[1..r]"
e2a := proc (el::{polynom, list}) global R;
    if type(el, rational) then
	  return el;
    elif type(el, linear) then
      return add(root_coords(el, R)[i]*a[i], i=1..rank(R));
    elif type(el, `*`) or type(el, list) then
	  return map(procname, el);
    elif type(el, `^`) then
	  return procname(op(1,el))^op(2,el);
    else
        print("error in e2a:",el);
        return infinity;
    end if;
end proc;

# convert vector in "e" into simple roots "a[1..r]"
a2e := proc (apol::{polynom, list}) global B;
    return eval(apol,[seq(a[i]=B[i],i=1..nops(B))]);
end proc:

# convert a-poly into w-poly
a2w := proc (apol::polynom) global R,B;
    return eval(apol, [seq(a[j]=add(weight_coords(B[j], R)[i]*w[i], i=1..nops(B)), j=1..nops(B))]);
end proc;

# convert w-poly into a-poly
w2a := proc (wpol::polynom) global R,B;
    return eval(wpol, [seq(w[j]=add(root_coords(weights(R)[j], R)[i]*a[i], i=1..nops(B)), j=1..nops(B))]);
end proc;

# degree of a polynomial in X[]
deg_X := proc(f::polynom) local d,max_d,term,temp,x,y;
    if type(f,`+`) then
        max_d:=0;
        for term in f do
            d := procname(term);
            if d>max_d then max_d:=d; end if;
        end do;
        return max_d;
    elif type(f,`^`) then
        procname(op(1,f))*op(2,f);
    else
        temp := f;
        for x in indets(f) do
            temp := eval(temp, x=y^(nops(op(1,x))));
        end do;
        return degree(temp);
    end if;
end proc:

# dimension of the standard representation of R
dimr := proc(R) local lie_type; option remember;
	lie_type := name_of(R);
    if lie_type = cat('A',rank(R)) then
        return rank(R)+1;
    elif lie_type = G2 then
        return 3;
    elif lie_type = E6 or lie_type = E7 then
        return 8;
    else
        return rank(R);
    end if;
end proc:

# positive roots relative to a parabolic subgroup
relative_roots := proc(R,roots::set) local L;
    L:={seq(base(R)[i],i=roots)};
    L:=orbit(L,R);
    return {op(pos_roots(R))} minus {op(L)};
end proc:

# vector to reflection
e2ref:=proc(el) local i,w; global R;
   vec2fc(reflect(el,interior_pt(R)),R,'w');
   return w;
end proc:

# action of a reduced word on a linear sum of ei
action:=proc(w::list,el::polynom) global B;
    return reflect(seq(B[i],i=w),el);
end proc:

# one line notation of elements in classical groups
oneline:=proc(weyl::list) local deg, lie_type, L, i; global R,pg;
	lie_type := name_of(R);
    if lie_type = cat('A',rank(R)) then
        deg := rank(R)+1;
    elif lie_type = cat('B',rank(R)) or lie_type = cat('C',rank(R)) or lie_type = cat('D',rank(R)) then
        deg := 2*rank(R);
    else
        return -infinity;
    end if;
    L:=convert(multperm(weyl,pg), 'permlist', deg);
    if lie_type = cat('B',rank(R)) or lie_type = cat('C',rank(R)) or lie_type = cat('D',rank(R)) then
        L:=L[-rank(R)..-1];
        for i from 1 to nops(L) do;
            if L[i]<=rank(R) then
                L[i]:=L[i]-rank(R)-1;
            else
                L[i]:=L[i]-rank(R);
            end if;
        end do;
    end if;
    return convert(L,array);
end proc:


end module:
