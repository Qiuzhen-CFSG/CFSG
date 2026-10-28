module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodeChiefQuotients
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PResidual.NormalComplement
public import Theory.GroupTheory.FixedElementaryTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.SpecificGroups.Held.LocalPairs.Faithfulness

/-!
# The original wreath quotient excludes a cyclic Xi automizer

The full two-core quotient is the binary-plane wreath group. Frattini
factorization identifies the image of the original complement normalizer
with the original Sylow image. The kernel of its action on the complement
lies in the quotient-map kernel: the odd core is self-centralizing in the
solvable quotient, and its intersection with a two-group is trivial.
Consequently a cyclic automizer would force the dihedral-eight Sylow image
to be cyclic, a contradiction.

This excludes the symplectic alternative of adequate 1.3.4 in the original
M22-code inside-core argument. The remaining exceptional and Held models
are centerless, without dropping any kernel in advance. The literal
Chapter12 application is `M22CodeCenterless`. Source: Aschbacher--Smith
8.2.2(1), printed p.715, and 1.3.4, pp.509--511, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem cyclic_automizer_forces_cyclic_image
    {H T P : Subgroup G} {Q : Type*} [Group Q] [Finite Q]
    (f : H →* Q) (hTH : T ≤ H) (_hPH : P ≤ H)
    (hs : Group.IsSolvable Q) (hcore : pCore 2 Q = ⊥)
    (hT : IsPGroup 2 T)
    (hodd : pPrimeCore 2 Q ≤ (P.subgroupOf H).map f)
    (himage : ((T ⊓ normalizer (P : Set G)).subgroupOf H).map f = (T.subgroupOf H).map f)
    (hc : IsCyclic (automizer T P)) : IsCyclic ((T.subgroupOf H).map f) := by
  let N := T ⊓ normalizer (P : Set G)
  have hNH : N ≤ H := inf_le_left.trans hTH
  let a := P.normalizerMonoidHom.comp (inclusion (show N ≤ normalizer (P : Set G) from inf_le_right))
  let r := f.comp (inclusion hNH)
  have hrange : r.range = (T.subgroupOf H).map f := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact himage
  have htwo : IsPGroup 2 ((T.subgroupOf H).map f) := hT.comap_subtype.map f
  have hdis : Disjoint ((T.subgroupOf H).map f) (pPrimeCore 2 Q) := by
    obtain ⟨n,hn⟩ := htwo.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hn]
    exact pPrimeCore_coprime_card.pow_left n
  have hk : a.rangeRestrict.ker ≤ r.ker := by
    intro x hx
    have hxC : (x : G) ∈ centralizer (P : Set G) := by
      have ha : inclusion (show N ≤ normalizer (P : Set G) from inf_le_right) x ∈
          P.normalizerMonoidHom.ker := congrArg Subtype.val hx
      rwa [normalizerMonoidHom_ker] at ha
    have hrC : r x ∈ centralizer (pPrimeCore 2 Q : Set Q) := by
      intro y hy
      obtain ⟨p,hp,rfl⟩ := hodd hy
      change f p * f (inclusion hNH x) = f (inclusion hNH x) * f p
      rw [←map_mul,←map_mul]
      exact congrArg f (Subtype.ext (hxC p hp))
    have ho : r x ∈ pPrimeCore 2 Q :=
      centralizer_pPrimeCore_le_of_pCore_eq_bot 2 hs hcore hrC
    have ht : r x ∈ (T.subgroupOf H).map f := hrange ▸ (show r x ∈ r.range from ⟨x,rfl⟩)
    exact hdis.le_bot ⟨ht,ho⟩
  let g := a.rangeRestrict.liftOfSurjective a.rangeRestrict_surjective ⟨r,hk⟩
  have hg (x : N) : g (a.rangeRestrict x) = r x :=
    a.rangeRestrict.liftOfRightInverse_comp_apply _ _ _ x
  have hgRange : g.range = r.range := by
    ext y
    constructor
    · rintro ⟨b,rfl⟩
      obtain ⟨x,rfl⟩ := a.rangeRestrict_surjective b
      exact hg x ▸ (show r x ∈ r.range from ⟨x,rfl⟩)
    · rintro ⟨x,rfl⟩
      exact ⟨a.rangeRestrict x,hg x⟩
  let : IsCyclic a.range := hc
  have hh : IsCyclic g.range := isCyclic_of_surjective g.rangeRestrict g.rangeRestrict_surjective
  rwa [hgRange,hrange] at hh

/-- The full original wreath quotient forces a noncyclic complement automizer. -/
theorem wreath_local_automizer_not_cyclic
    (S : Sylow 2 G) {H P C : Subgroup G} (hSH : (S : Subgroup G) ≤ H)
    (hin : LocalInput 3 (S : Subgroup G) ((pResidual 2 H).map H.subtype) P C)
    (hs : Group.IsSolvable H)
    (f : H →* WreathTwoResidual.Actor) (hf : Function.Surjective f)
    (hk : f.ker = pCore 2 H) : ¬ IsCyclic (automizer (S : Subgroup G) P) := by
  let X := (pResidual 2 H).map H.subtype
  have hXH : X ≤ H := map_subtype_le _
  have hPH : P ≤ H := (show P ≤ X from le_sup_right.trans hin.complement.le).trans hXH
  have hNH : (S : Subgroup G) ⊓ normalizer (P : Set G) ≤ H := inf_le_left.trans hSH
  have hHX : H ≤ normalizer (X : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hQH : X.pCoreIn 2 ≤ H := (pCoreIn_le 2 X).trans hXH
  have hQker : (X.pCoreIn 2).subgroupOf H ≤ f.ker := by
    rw [hk]
    have hh := pCoreIn_mono_of_normalizes (p := 2) hXH hHX
    intro x hx
    obtain ⟨y,hy,he⟩ := hh hx
    have heq : y = x := Subtype.ext he
    exact heq ▸ hy
  have hQimage : ((X.pCoreIn 2).subgroupOf H).map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr hQker
  have hPimage : (P.subgroupOf H).map f = pResidual 2 WreathTwoResidual.Actor := by
    have he := congrArg (fun A : Subgroup G => (A.subgroupOf H).map f) hin.complement
    rw [subgroupOf_sup hQH hPH,Subgroup.map_sup,hQimage,bot_sup_eq] at he
    rw [show X.subgroupOf H = pResidual 2 H from
      comap_map_eq_self_of_injective H.subtype_injective _,map_pResidual_of_surjective 2 f hf] at he
    exact he
  have hNimage : (((S : Subgroup G) ⊓ normalizer (P : Set G)).subgroupOf H).map f =
      (((S : Subgroup G)).subgroupOf H).map f := by
    have he := congrArg (fun A : Subgroup G => (A.subgroupOf H).map f) hin.normalizer_factor
    rw [subgroupOf_sup hQH hNH,Subgroup.map_sup,hQimage,bot_sup_eq] at he
    exact he.symm
  intro hc
  have hcy := cyclic_automizer_forces_cyclic_image f hSH hPH
    (by let := hs; exact Group.isSolvable_of_surjective hf)
    WreathTwoResidual.twoCore_eq_bot S.isPGroup'
    (hPimage.symm ▸ pPrimeCore_le_pResidual) hNimage hc
  let R := (S.subtype hSH).mapSurjective hf
  have hcy' : IsCyclic R := hcy
  obtain ⟨e⟩ := wreath_two_sylow_mulEquiv_dihedral_four R
  let : IsCyclic R := hcy'
  let : IsCyclic (DihedralGroup 4) := isCyclic_of_surjective e.toMonoidHom e.surjective
  have he : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 =
      DihedralGroup.sr 0 * DihedralGroup.r (1 : ZMod 4) := mul_comm _ _
  exact (by decide : DihedralGroup.r (1 : ZMod 4) * DihedralGroup.sr 0 ≠
    DihedralGroup.sr 0 * DihedralGroup.r (1 : ZMod 4)) he


private theorem center_eq_bot_of_marking {Q R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (hz : center R = ⊥) : center Q = ⊥ := by
  have hh := FixedElementary.map_center e
  rw [hz] at hh
  exact (map_eq_bot_iff_of_injective _ e.injective).mp hh

/-- The remaining intrinsic Xi models have no central covering kernel. -/
theorem exceptional_or_held_center_eq_bot {Q : Type*} [Group Q]
    (h : ExceptionalModel Q ∨ Nonempty (Q ≃* Held.He)) : center Q = ⊥ := by
  rcases h with hm | hm
  · rcases hm with hm | hm | hm
    · exact center_eq_bot_of_marking hm.some Sporadic.Mathieu.m11_center_eq_bot
    · obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
      let _ := Atlas.sl_perfect (F := F) 4 (by decide)
      exact center_eq_bot_of_marking e
        (Group.IsPerfect.center_quotient_center_eq_bot (Matrix.SpecialLinearGroup (Fin 4) F))
    · obtain ⟨F,_,_,_,⟨e⟩⟩ := hm
      let _ := Atlas.sl_perfect (F := F) 5 (by decide)
      exact center_eq_bot_of_marking e
        (Group.IsPerfect.center_quotient_center_eq_bot (Matrix.SpecialLinearGroup (Fin 5) F))
  · exact center_eq_bot_of_marking hm.some Held.LocalPairs.center_eq_bot

end CFSG.Quasithin.Chapter8.MathieuShadowRows

