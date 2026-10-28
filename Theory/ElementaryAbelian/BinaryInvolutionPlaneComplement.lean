module
public import Theory.LinearAlgebra.BinaryInvolutionPlaneComplement
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.ByContra

/-!
# An invariant complement to a moved elementary four-group

For a normalizing involution, a moved elementary four-group is its binary
Jordan plane. The linear equivariant retraction gives an invariant subgroup
complement. The ambient endpoint retains the original subgroup inclusions
and conjugating involution, for the local splitting preceding Gaschütz.

Source: Aschbacher–Smith, Quasithin Groups, 14.3.19(9), printed p.997.
-/

open Module Submodule LinearMap

open scoped IsMulCommutative
public theorem IsElementaryAbelian.exists_invariant_complement_of_moved_four
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (a : MulAut E) (ha : a^2=1) (V : Subgroup E) (hV:Nat.card V=4)
    (hAV:V.map a.toMonoidHom=V) (hm:∃v∈V,a v≠v) :
    ∃ D : Subgroup E, IsCompl V D ∧ D.map a.toMonoidHom=D := by
  classical
  let b : Additive E ≃ₗ[ZMod 2] Additive E :=
    { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
  have haa (x:E):a (a x)=x := congrArg (fun c:MulAut E=>c x) (by simpa only [pow_two] using ha)
  have hbb:b*b=1 := LinearEquiv.ext fun x=>haa x
  obtain ⟨v,hv,hvm⟩:=hm
  let w : Additive E := Additive.ofMul v
  have hwm:b w≠w := hvm
  have hw:w≠0 := by intro he;apply hwm;rw [he,map_zero]
  have hbw:b w≠0 := fun he=>hw (b.injective (he.trans b.map_zero.symm))
  let φ : AddSubgroup (Additive E) ≃o Submodule (ZMod 2) (Additive E) :=
    AddSubgroup.toZModSubmodule 2
  let U:=φ V.toAddSubgroup
  have hvU:w∈U := hv
  have havU:b w∈U := by
    change a v∈V
    rw [←hAV]
    exact Subgroup.mem_map_of_mem a.toMonoidHom hv
  let P:=Submodule.span (ZMod 2) ({w,b w}:Set (Additive E))
  have hPU:P≤U := Submodule.span_le.mpr (by
    intro x hx
    rcases (show x=w ∨ x=b w from by simpa using hx) with rfl|rfl
    · exact hvU
    · exact havU)
  have hli:LinearIndependent (ZMod 2) ![w,b w] := by
    apply (LinearIndependent.pair_iff' hw).mpr
    intro t ht
    fin_cases t
    · change (0:ZMod 2) • w=b w at ht
      exact hbw (by simpa only [zero_smul] using ht.symm)
    · change (1:ZMod 2) • w=b w at ht
      exact hwm (by simpa only [one_smul] using ht.symm)
  have hrange:Set.range ![w,b w]=({w,b w}:Set (Additive E)) := by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · intro hx
      rcases (show x=w ∨ x=b w from by simpa using hx) with rfl|rfl
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have hPdim:Module.finrank (ZMod 2) P=2 := by
    change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) ({w,b w}:Set (Additive E)))=2
    rw [←hrange]
    exact finrank_span_eq_card hli
  have hUc:Nat.card U=4 := hV
  have hUdim:Module.finrank (ZMod 2) U=2 := by
    have hh:=Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=U)
    rw [Nat.card_zmod,hUc] at hh
    exact Nat.pow_right_injective (by decide:1<2) (by simpa using hh.symm)
  have hPUeq:P=U := Submodule.eq_of_le_of_finrank_le hPU (by rw [hUdim,hPdim])
  obtain ⟨C,hC,hstable⟩:=b.exists_invariant_complement_of_binary_moved_plane hbb w hwm
  change IsCompl P C at hC
  rw [hPUeq] at hC
  let D:Subgroup E := (φ.symm C).toSubgroup
  have hd:IsCompl V D := IsCompl.of_orderEmbedding (RelIso.toRelEmbedding Subgroup.toAddSubgroup)
    ((φ.isCompl_iff).mpr (show IsCompl (φ V.toAddSubgroup) (φ (φ.symm C)) from by
      rwa [φ.apply_symm_apply]))
  have had (x:E) (hx:x∈D):a x∈D := hstable (Additive.ofMul x) hx
  refine ⟨D,hd,le_antisymm ?_ ?_⟩
  · rintro x ⟨y,hy,rfl⟩
    exact had y hy
  · intro x hx
    exact ⟨a x,had x hx,haa x⟩


namespace Subgroup
public theorem exists_invariant_complement_of_normalizing_involution_four
    {G:Type*} [Group G] [Finite G]
    (B V:Subgroup G) [IsElementaryAbelian 2 B] (hVB:V≤B) (hV:Nat.card V=4)
    (u:G) (hu:u^2=1) (huB:u∈normalizer (B:Set G)) (huV:u∈normalizer (V:Set G))
    (hmove:u∉centralizer (V:Set G)) :
    ∃D:Subgroup G,D≤B ∧ Disjoint V D ∧ V⊔D=B ∧ u∈normalizer (D:Set G) := by
  let a:=B.normalizerMonoidHom ⟨u,huB⟩
  have ha:a^2=1 := by
    change B.normalizerMonoidHom ⟨u,huB⟩^2=1
    rw [←map_pow,show (⟨u,huB⟩:normalizer (B:Set G))^2=1 from Subtype.ext hu,map_one]
  have htransport (E:Subgroup B) :
      (E.map a.toMonoidHom).map B.subtype=(E.map B.subtype).map (MulAut.conj u).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  let W:=V.subgroupOf B
  have hW:Nat.card W=4 := by rw [Nat.card_congr (subgroupOfEquivOfLe hVB).toEquiv,hV]
  have hWmap:W.map B.subtype=V := map_subgroupOf_eq_of_le hVB
  have hWa:W.map a.toMonoidHom=W := by
    apply map_injective B.subtype_injective
    rw [htransport,hWmap]
    exact mem_normalizer_iff_map_conj_eq.mp huV
  have hm:∃v∈W,a v≠v := by
    by_contra! h
    apply hmove
    intro v hv
    have he:=congrArg (fun x:B=>(x:G)) (h ⟨v,hVB hv⟩ hv)
    change u*v*u⁻¹=v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨D,hD,hDa⟩:=IsElementaryAbelian.exists_invariant_complement_of_moved_four a ha W hW hWa hm
  refine ⟨D.map B.subtype,map_subtype_le D,?_,?_,?_⟩
  · rw [←hWmap]
    exact disjoint_map B.subtype_injective hD.disjoint
  · rw [←hWmap,←map_sup,hD.sup_eq_top,←MonoidHom.range_eq_map,B.range_subtype]
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change (D.map B.subtype).map (MulAut.conj u).toMonoidHom=D.map B.subtype
    rw [←htransport,hDa]
end Subgroup
