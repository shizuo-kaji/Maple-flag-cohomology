# # Draw weak and strong Bruhat diagram
# # by Shizuo Kaji

# it requires "coxeter and weyl" and "poset" packages by J.Stembridge

# http://www.math.lsa.umich.edu/~jrs/maple.html

with(posets);
with(coxeter); with(weyl);
with(WeylOps):

# Draw weak (left or right) bruhat diagram
#
# Example:
# H,L := wbruhat(F4, {}, 'L')
# plot_poset(H, labels = L, stretch = 1)

wbruhat:=proc(R,roots::set:={}, lr::symbol:='L', upto::integer :=0)
             local H,i,j,w,newweyl,oldweyl,p,pos,wlabel,udim;
  udim := `if`(upto>0,upto,nops(pos_roots(R)));
  wlabel:=[[]]; oldweyl:=[[]];
  H:=NULL;
  while nops(wlabel[-1])<udim and nops(oldweyl)>0 do
    newweyl:=[];
  	for i  from 1 to nops(oldweyl) do
	    for j in {$1..rank(R)} minus roots do
	    	w:=`if`(lr='L',reduce([j,op(oldweyl[i])],R),reduce([op(oldweyl[i]),j],R));
			if nops(w)=nops(oldweyl[i])+1 then
				if not member(w, newweyl, 'pos') then
					H:=H, [nops(wlabel)-nops(oldweyl)+i, nops(wlabel)+nops(newweyl)+1];
					newweyl:=[op(newweyl), w];
				else
					H:=H, [nops(wlabel)-nops(oldweyl)+i, nops(wlabel)+pos];
				end if;
			end if;
	    end do;
	end do;
    wlabel:=[op(wlabel), op(newweyl)]; oldweyl:=newweyl;
  end do;
  return {H},table([seq(i = convert(wlabel[i], 'string'), i = 1 .. nops(wlabel))]):
end proc:

# Draw strong bruhat diagram
#
# Example:
# H,L,E := wbruhat(F4, {}, 3)
# plot_poset(H, labels = L, stretch = 1)
# E contains edge labeling

sbruhat := proc (R, roots::set:={}, upto::integer:=0)
local H, w, r, v, i, j, beta, pos, newvects, newreps, vects,
    len, reps, oldvects, oldreps, edge, udim,B,P;

    B := base(R); r := nops(B); P:=pos_roots(R);
    udim := `if`(upto>0,upto,nops(P));
	newvects := [add(weights(R)[i], i={$1..r} minus roots)];
    newreps := []; reps := [[]]; vects := newvects;

    for len from 1 to udim do;
		oldvects := newvects; oldreps := [newreps];
		newvects := []; newreps := NULL;
		for j to nops(oldvects) do
			for i to r do
				if 0 < iprod(B[i], oldvects[j]) then
					v := reflect(B[i], oldvects[j]);
					if not member(v, newvects) then
						newvects := [op(newvects), v];
						newreps := newreps, reduce([i, op(oldreps[j])], R)
					end if
				end if
			end do
		end do;
		if newreps=NULL then break; end if;
        reps := [op(reps), newreps];
        vects := [op(vects), op(newvects)];
    end do;

    H:= NULL;
    for j from 1 to nops(vects) do
        for beta in P do
            if iprod(beta,vects[j])>0 then
                v:=reflect(beta,vects[j]);
                if member(v,vects,'pos') then
                    edge[j,pos]:=root_coords(beta,R);
                    H:= H, [j,pos];
                end if;
            end if;
        end do;
    end do;
    return {H},table([seq(i=[i,reps[i]],i=1..nops(reps))]),edge;
end proc;



# check if v is minimal w.r.t. a reflection subgroup;
has_descent:=proc(w::list,refsub_gen::set,R) local ref;
  for ref in refsub_gen do
    if nops(reduce([op(w),op(ref)],R))<nops(w) then return true; end if;
 end do;
 return false;
end proc:

# reduced word w.r.t. a reflection subgroup
ref_reduce:=proc(w::list,refsub_gen::set,R) local u,v,neww,is_min;
    neww:=reduce(w,R);
    is_min:=false;
    while is_min=false do;
        is_min:=true;
        for u in refsub_gen do
            v:=reduce([op(neww),op(u)],R);
            if nops(v)<nops(neww) then
                neww:=v;
                is_min:=false;
            end if;
        end do;
    end do;
    return neww;
end proc:

# strong bruhat graph w.r.t. a reflection subgroup geenrated by
# (non-simple) roots
refbruhat:=proc(R,refsub::set:={},upto::integer:=0) local H,i,j,r,u,v,w,len,
    reps,newreps,oldreps,vects,newvects,oldvects,refsub_gen,udim,pos,ref,P,B,edge;
    B:=base(R); r:=rank(R);
    P:=pos_roots(R);
    udim := `if`(upto>0,upto,nops(P));

    refsub_gen:={};
    for ref in refsub do;
        vec2fc(reflect(ref,interior_pt(R)),B,'w');
        refsub_gen:={op(refsub_gen),w};
    end do;

    # enumerate reduced words
	newvects := {interior_pt(R)};
    reps := [[]]; newreps := reps; vects := newvects;

    for len from 1 to udim do;
		oldvects := newvects; oldreps := newreps;
		newvects := []; newreps := [];
		for j to nops(oldvects) do
			for i to r do
				if 0 < iprod(B[i], oldvects[j]) then
                    v := reflect(B[i], oldvects[j]);
                    w := reduce([i, op(oldreps[j])], R);
					if not member(v, newvects) then
                        if not has_descent(w,refsub_gen,R) then
                            newreps := [op(newreps), w];
                            newvects := [op(newvects), v];
                        end if;
					end if
				end if
			end do
		end do;
		if newreps={} then break; end if;
        reps := [op(reps), op(newreps)];
        vects := [op(vects), op(newvects)];
    end do;

    # edges
    H:=NULL;
    for j from 1 to nops(vects) do;
        for ref in P do
            if iprod(ref,vects[j])<0 then next; end if;
            vec2fc(reflect(ref,vects[j]),R,'w');
            w:=ref_reduce(w,refsub_gen,R):
            member(w,reps,'pos');
            if j<pos then
                if assigned(edge[j,pos]) then
                    edge[j,pos]:=[op(edge[j,pos]),root_coords(ref,R)];
                else
                    edge[j,pos]:=[root_coords(ref,R)];
                    H:=H, [j,pos];
                end if
            end if;
        end do;
    end do;
    return {H},table([seq(i = [i,reps[i]], i = 1 .. nops(reps))]),edge:
end proc:



