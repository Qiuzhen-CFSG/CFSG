module

public import Theory.GroupTheory.CComponent.RadicalStabilizer
public import Theory.GroupTheory.SylowNormalRestriction
public import Mathlib.GroupTheory.Nilpotent
public import Theory.GroupTheory.PGroup.CommutingConjugateDisplacement
public import Theory.GroupTheory.SylowKernelCore

/-!
# The moving-component displacement in C.2.4

Put R = N_Q(L). When Q meets L in less than a Sylow subgroup, the
p-group normalizer condition supplies a two-element y outside R in
Y = N_{LR}(R). The literal component-stabilizer theorem gives O₂(Y)=R.
Normality of N_G(L) makes R normal in Q, so a mover s in Q normalizes R.

Distinct component conjugates commute modulo O₂(G), which lies in R.
Hence the images of Y and Y^s commute in N_G(R)/R. Its image of Y has
trivial two-core, so y and y^s cannot have the same image. Their displacement
is a nontrivial two-element in the quotient and lifts through the two-group
R. All witnesses retain their original ambient locations, for use with
the normal-closure Sylow hypothesis in the CPU contradiction.

Source: Aschbacher, *Pushing-up in finite groups*, Math. Z. 177 (1981),
8.2(5) and 10.3, printed p.78; Aschbacher--Smith C.2.4(2).
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

private theorem exists_two_element_normalizer_outside
    (K R : Subgroup G) (hRK : R ≤ K) (hp : IsPGroup 2 R)
    (hnot : ¬ ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype = R) :
    ∃ y : G, y ∈ K ⊓ normalizer (R : Set G) ∧ y ∉ R ∧
      IsPGroup 2 (zpowers y) := by
  obtain ⟨S,hS⟩ := (hp.comap_subtype (K := K)).exists_le_sylow
  let P := R.subgroupOf ((S : Subgroup K).map K.subtype)
  let S₀ := (S : Subgroup K).map K.subtype
  have hRS : R ≤ S₀ := by
    intro r hr
    exact mem_map_of_mem K.subtype (hS (show (⟨r,hRK hr⟩ : K) ∈ R.subgroupOf K from hr))
  have hne : S₀ ≠ R := fun he => hnot ⟨S,he⟩
  have hproper : P < ⊤ := lt_top_iff_ne_top.mpr fun he =>
    hne (le_antisymm (subgroupOf_eq_top.mp he) hRS)
  let : Group.IsNilpotent S₀ := (S.isPGroup'.map K.subtype).isNilpotent
  obtain ⟨y,hyN,hy⟩ := SetLike.exists_of_lt (Group.normalizerCondition_of_isNilpotent P hproper)
  have hyN' : (y : G) ∈ normalizer (R : Set G) := by
    have hh := P.le_normalizer_map S₀.subtype (mem_map_of_mem S₀.subtype hyN)
    rwa [map_subgroupOf_eq_of_le hRS] at hh
  refine ⟨y,⟨map_subtype_le _ y.property,hyN'⟩,hy,?_⟩
  exact (S.isPGroup'.map K.subtype).to_le (zpowers_le.mpr y.property)

private theorem not_sylow_join_of_not_component_intersection
    (Q L : Subgroup G)
    (hnot : ¬ ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = Q ⊓ L) :
    let R := Q ⊓ normalizer (L : Set G)
    ¬ ∃ S : Sylow 2 (L ⊔ R : Subgroup G),
      (S : Subgroup (L ⊔ R : Subgroup G)).map (L ⊔ R : Subgroup G).subtype = R := by
  let R := Q ⊓ normalizer (L : Set G)
  let K := L ⊔ R
  let L₀ := L.subgroupOf K
  let : L₀.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer (show R ≤ normalizer (L : Set G) from inf_le_right))
  change ¬ ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype = R
  rintro ⟨S,hS⟩
  obtain ⟨T,hT⟩ := S.exists_sylow_map_eq_inf_of_normal L₀
  let e : L₀ ≃* L := subgroupOfEquivOfLe (show L ≤ K from le_sup_left)
  refine hnot ⟨T.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((T : Subgroup L₀).map e.toMonoidHom).map L.subtype = _
  have he : L.subtype.comp e.toMonoidHom = K.subtype.comp L₀.subtype := rfl
  rw [map_map, he, ← map_map, hT]
  rw [Subgroup.map_inf _ _ K.subtype K.subtype_injective, hS, map_subgroupOf_eq_of_le (show L ≤ K from le_sup_left)]
  exact le_antisymm (inf_le_inf_right _ inf_le_left)
    (fun x hx => ⟨⟨hx.1,L.le_normalizer hx.2⟩,hx.2⟩)


private theorem component_conjugate_commutator_le_core {L : Subgroup G}
    (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    {s : G} (hs : s ∉ normalizer (L : Set G)) :
    ⁅L,L.map (MulAut.conj s).toMonoidHom⁆ ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let := pCore_isNilpotent (p := 2) (G := G)
  have hC : IsComponent (G ⧸ pCore 2 G) (L.map q) :=
    ⟨hL.subnormal.quotient, IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hL)⟩
  have hsn : q s ∉ normalizer (L.map q : Set (G ⧸ pCore 2 G)) := by
    intro hh
    apply hs
    rw [← normalizer_cComponent_quotient hL (pCore 2 G)]
    exact hh
  have he : (L.map (MulAut.conj s).toMonoidHom).map q =
      (L.map q).map (MulAut.conj (q s)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  have hne : L.map q ≠ (L.map q).map (MulAut.conj (q s)).toMonoidHom :=
    fun hh => hsn (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  have hc := hC.commutator_eq_bot_of_ne (hC.map_conj (q s)) hne
  rw [← he, ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hc
  exact hc

omit [Finite G] in
private theorem commutator_sup_normal_le
    {A R : Subgroup G} [R.Normal] (s : G)
    (hc : ⁅A,A.map (MulAut.conj s).toMonoidHom⁆ ≤ R) :
    ⁅A ⊔ R,(A ⊔ R).map (MulAut.conj s).toMonoidHom⁆ ≤ R := by
  let q := QuotientGroup.mk' R
  have hker : q.ker = R := QuotientGroup.ker_mk' R
  have he (D : Subgroup G) : (D.map (MulAut.conj s).toMonoidHom).map q =
      (D.map q).map (MulAut.conj (q s)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  have hbot : (⁅A,A.map (MulAut.conj s).toMonoidHom⁆).map q = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (hker.symm ▸ hc)
  apply (show (⁅A ⊔ R,(A ⊔ R).map (MulAut.conj s).toMonoidHom⁆ ≤ q.ker) →
    (⁅A ⊔ R,(A ⊔ R).map (MulAut.conj s).toMonoidHom⁆ ≤ R) from fun h => h.trans hker.le)
  apply (Subgroup.map_eq_bot_iff _ (f := q)).mp
  rw [map_commutator,he,Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq]
  rwa [map_commutator,he] at hbot

/-- The literal two-element displacement outside the radical stabilizer. -/
theorem moving_component_displacement {Q L : Subgroup G}
    (hq : IsPRadical 2 Q) (hL : L.IsCComponent)
    [IsQuasisimple (L ⧸ pCore 2 L)] [(normalizer (L : Set G)).Normal]
    (hmove : ¬ Q ≤ normalizer (L : Set G))
    (hnot : ¬ ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = Q ⊓ L) :
    let R := Q ⊓ normalizer (L : Set G)
    ∃ y s : G, y ∈ (L ⊔ R) ⊓ normalizer (R : Set G) ∧ s ∈ Q ∧
      IsPGroup 2 (zpowers (y⁻¹ * (s * y * s⁻¹))) ∧
      y⁻¹ * (s * y * s⁻¹) ∈ normalizer (R : Set G) ∧
      y⁻¹ * (s * y * s⁻¹) ∈ normalizer (L : Set G) ∧
      y⁻¹ * (s * y * s⁻¹) ∉ R := by
  classical
  let R := Q ⊓ normalizer (L : Set G)
  let N := normalizer (R : Set G)
  let Y := (L ⊔ R) ⊓ N
  have hRp : IsPGroup 2 R := hq.isPGroup.to_le inf_le_left
  have hQR : Q ≤ N := (le_inf Q.le_normalizer le_normalizer_of_normal).trans
    inf_normalizer_le_normalizer_inf
  obtain ⟨y,hy,hyR,hyp⟩ := exists_two_element_normalizer_outside (L ⊔ R) R le_sup_right
    hRp (not_sylow_join_of_not_component_intersection Q L hnot)
  obtain ⟨s,hs,hsL⟩ := SetLike.not_le_iff_exists.mp hmove
  have hyN : y ∈ N := hy.2
  have hsN : s ∈ N := hQR hs
  let R₀ := R.subgroupOf N
  let Y₀ := Y.subgroupOf N
  let D := L.subgroupOf N
  let : R₀.Normal := normal_subgroupOf_of_le_normalizer (show N ≤ normalizer (R : Set G) from le_rfl)
  let y₀ : N := ⟨y,hyN⟩
  let s₀ : N := ⟨s,hsN⟩
  have hcore : Y₀.pCoreIn 2 = R₀ := by
    apply map_injective N.subtype_injective
    rw [map_pCoreIn_of_injective 2 Y₀ N.subtype N.subtype_injective, map_subgroupOf_eq_of_le (show Y ≤ N from inf_le_right),
      hL.stabilizer_radical hq, map_subgroupOf_eq_of_le R.le_normalizer]
  have hYR : Y₀ = D ⊔ R₀ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨l,hl,r,hr,he⟩ := (show (x : G) ∈ (L : Set G) * (R : Set G) by
        rw [← coe_mul_of_right_le_normalizer_left L R (show R ≤ normalizer (L : Set G) from inf_le_right)]
        exact hx.1)
      have hlN : l ∈ N := by
        have hh := N.mul_mem x.property (N.inv_mem (R.le_normalizer hr))
        rwa [← he,mul_inv_cancel_right] at hh
      have hprod : (⟨l,hlN⟩ : N) * ⟨r,R.le_normalizer hr⟩ = x := Subtype.ext he
      exact hprod ▸ mul_mem (mem_sup_left hl) (mem_sup_right hr)
    · exact sup_le (fun _ hx => ⟨mem_sup_left hx, (Subtype.prop _)⟩)
        (fun _ hx => ⟨mem_sup_right hx, (Subtype.prop _)⟩)
  have hcoreR : pCore 2 G ≤ R := le_inf
    (pCore_le_of_pCore_normalizer_le Q hq.isPGroup hq.2.le) (by
      let := pCore_isNilpotent (p := 2) (G := G)
      rw [← normalizer_cComponent_quotient hL (pCore 2 G)]
      intro x hx
      rw [mem_comap]
      have hkx : x ∈ (QuotientGroup.mk' (pCore 2 G)).ker := by
        rwa [QuotientGroup.ker_mk']
      rw [MonoidHom.mem_ker.mp hkx]
      exact one_mem _)
  have hD : ⁅D,D.map (MulAut.conj s₀).toMonoidHom⁆ ≤ R₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator]
    have hm : (D.map (MulAut.conj s₀).toMonoidHom).map N.subtype ≤
        L.map (MulAut.conj s).toMonoidHom := by
      rw [map_map]
      rintro _ ⟨d,hd,rfl⟩
      exact mem_map_of_mem _ hd
    exact (commutator_mono (by rw [subgroupOf_map_subtype]; exact inf_le_left) hm).trans
      ((component_conjugate_commutator_le_core hL hsL).trans hcoreR)
  have hcomm : ⁅Y₀,Y₀.map (MulAut.conj s₀).toMonoidHom⁆ ≤ R₀ := by
    rw [hYR]
    exact commutator_sup_normal_le s₀ hD
  have hyp₀ : IsPGroup 2 (zpowers y₀) := by
    have hh := hyp.comap_of_injective N.subtype N.subtype_injective
    exact hh.to_le (zpowers_le.mpr (mem_zpowers y))
  have hd := p_displacement_modulo_normal R₀ Y₀ hRp.comap_subtype hcore s₀ y₀ hy
    hyR hyp₀ hcomm
  have hyL : y ∈ normalizer (L : Set G) := (sup_le L.le_normalizer inf_le_right) hy.1
  have hsyl : s * y * s⁻¹ ∈ normalizer (L : Set G) :=
    (inferInstance : (normalizer (L : Set G)).Normal).conj_mem _ hyL s
  refine ⟨y,s,hy,hs,?_,N.mul_mem (N.inv_mem hyN) (N.mul_mem (N.mul_mem hsN hyN) (N.inv_mem hsN)),
    (normalizer (L : Set G)).mul_mem ((normalizer (L : Set G)).inv_mem hyL) hsyl,hd.2⟩
  have hh := hd.1.map N.subtype
  rw [MonoidHom.map_zpowers] at hh
  exact hh

end CFSG.Quasithin.ChapterC.Section02Source

