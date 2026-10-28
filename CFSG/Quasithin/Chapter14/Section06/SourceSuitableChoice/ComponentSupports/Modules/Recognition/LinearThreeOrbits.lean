module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeCovers
public import Theory.Representation.BinaryOffender.Homogeneous.LinearThreeInertia

/-!
# The original two-support orbit of a terminal linear-three seed

The component normalizer has exactly the expected image in H/O₂(H).
Inner/graph automorphism coverage then bounds a homogeneous natural-cover
seed's orbit by two actual subspaces. The original quotient coordinates
lift this to an equality of literal conjugate spans of subgroups of U.
Their total quotient dimension is at most eight, retaining each possible
central covering line. A lifted support is normalized exactly when the
induced automorphism of the component image is inner.

At H=Mc, the original hypotheses construct the marked seed and apply all
these results without additional module premises. Identifying its orbit
with the entire component support, excluding four-dimensional covers and
FF alternatives, and suitable-vector assembly remain with
qt-e-suitable-component-supports. Original14.6.18 remains the explicit
input discharged by qt-e-14625-source; the same eventual suitable vector
must serve every downstream support consumer.

Source: Aschbacher--Smith A.1.40--42, F.9.18 and14.6.22--24,
printed pp.31--32,325--326 and1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv


omit hG hempty hM hunique hmany hcard e hab hsolv in
/-- The component normalizer commutes with passage to the literal two-core quotient. -/
theorem source_component_normalizer_image
    (H : Subgroup G) (_hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    actorImage H ((T : Subgroup G) ⊓ normalizer (K : Set G)) =
      actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H)) := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hn := normalizer_cComponent_quotient hK (pCore 2 H)
  rw [←subgroupOf_normalizer_eq hKH] at hn
  apply le_antisymm
  · rintro x ⟨t,ht,rfl⟩
    refine ⟨⟨t,ht.1,rfl⟩,?_⟩
    change t ∈ (normalizer ((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))).comap
      (QuotientGroup.mk' (pCore 2 H))
    rw [hn]
    exact ht.2
  · rintro x ⟨⟨t,ht,rfl⟩,hnorm⟩
    refine ⟨t,⟨ht,?_⟩,rfl⟩
    change t ∈ (normalizer (K : Set G)).subgroupOf H
    rw [←hn]
    exact hnorm

omit hG hempty hM hunique hmany hcard e hab hsolv in
/-- All conjugates of a homogeneous component seed under N_T(K) are one
of two literal original subgroups, with central kernels retained. -/
theorem source_seed_two_conjugates
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation (actorImage H K)
      (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
    (b : (actorImage H K) ≃* Matrix.PSL3Two.SL)
    (hdim : Module.finrank (ZMod 2) I ≤ 4) :
    let c := originalSection a
    let W := c.subspacePreimage I
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    ∃ t : S,
      (∀ s : S, W.map (MulAut.conj (s:G)⁻¹).toMonoidHom = W ∨
        W.map (MulAut.conj (s:G)⁻¹).toMonoidHom = W.map (MulAut.conj (t:G)⁻¹).toMonoidHom) ∧
      conjugateSpanBy W S = W ⊔ W.map (MulAut.conj (t:G)⁻¹).toMonoidHom ∧
      Module.finrank (ZMod 2) (c.imageSpace (conjugateSpanBy W S)) ≤ 8 := by
  let c := originalSection a
  let W := c.subspacePreimage I
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let R := actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
  have hSH : S ≤ H := inf_le_left.trans hH.1.2
  have hR : actorImage H S = R := source_component_normalizer_image T H hH K hKH hK
  obtain ⟨t,ht⟩ := hI.linear_three_conjugates a.representation b
  have htR : t.val ∈ actorImage H S := hR.symm ▸ t.property
  obtain ⟨u,hu,he⟩ := htR
  let t₀ : S := ⟨(u:G)⁻¹,S.inv_mem hu⟩
  have hpair (s : S) : W.map (MulAut.conj (s:G)⁻¹).toMonoidHom = W ∨
      W.map (MulAut.conj (s:G)⁻¹).toMonoidHom = W.map (MulAut.conj (t₀:G)⁻¹).toMonoidHom := by
    let v : H := ⟨(s:G)⁻¹,hSH (S.inv_mem s.property)⟩
    let q := QuotientGroup.mk' (pCore 2 H)
    have hqv : q v ∈ R := hR ▸ (show q v ∈ actorImage H S from ⟨v,S.inv_mem s.property,rfl⟩)
    have hp := ht ⟨q v,hqv⟩
    have hv : W.map (MulAut.conj (s:G)⁻¹).toMonoidHom = c.subspacePreimage (I.map (a.representation (q v))) :=
      (c.subspacePreimage_map I v).symm
    have hu' : W.map (MulAut.conj (t₀:G)⁻¹).toMonoidHom = c.subspacePreimage (I.map (a.representation t.val)) := by
      have hc := c.subspacePreimage_map I u
      change c.subspacePreimage (I.map (a.representation (q u))) = W.map (MulAut.conj (u:G)).toMonoidHom at hc
      rw [he] at hc
      simpa only [t₀,inv_inv] using hc.symm
    rw [hv,hu']
    exact hp.elim (fun hh => Or.inl (congrArg c.subspacePreimage hh))
      (fun hh => Or.inr (congrArg c.subspacePreimage hh))
  refine ⟨t₀,hpair,?_,?_⟩
  · rw [conjugateSpanBy_eq_iSup_conj]
    apply le_antisymm
    · apply iSup_le
      intro s
      have hh := hpair s⁻¹
      simp only [Subgroup.coe_inv,inv_inv] at hh
      exact hh.elim (fun h => h ▸ le_sup_left) (fun h => h ▸ le_sup_right)
    · apply sup_le
      · exact le_trans (by rw [Subgroup.conjBy_one] : W ≤ W.conjBy (1:G))
          (le_iSup (fun s : S => W.conjBy s.val) 1)
      · exact le_iSup (fun s : S => W.conjBy s.val) t₀⁻¹
  · rw [originalSection_support_orbit a S hSH I,hR]
    exact (hI.linear_three_orbit_finrank_le a.representation b).trans (by omega)

omit hG hempty hM hunique hmany hcard e hab hsolv in
/-- The normalizer of the literal lifted natural cover consists exactly
of the elements inducing inner automorphisms on the actual component image. -/
theorem source_seed_normalizer_iff_inner
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation (actorImage H K)
      (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage H K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3))
    (s : ((T : Subgroup G) ⊓ normalizer (K : Set G) : Subgroup G)) :
    (s:G) ∈ normalizer ((originalSection a).subspacePreimage I : Set G) ↔
      ∃ k : actorImage H K, ∀ x : actorImage H K,
        let q := QuotientGroup.mk' (pCore 2 H) ⟨s,hH.1.2 s.property.1⟩
        q * x.val * q⁻¹ = k.val * x.val * k.val⁻¹ := by
  let g : H := ⟨s,hH.1.2 s.property.1⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
  have hg : q g ∈ R := by
    change q g ∈ actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
    rw [←source_component_normalizer_image T H hH K hKH hK]
    exact ⟨g,s.property,rfl⟩
  let t : R := ⟨q g,hg⟩
  rw [(originalSection a).mem_normalizer_subspacePreimage_iff I g]
  have hh := hI.natural_map_eq_iff_inner a.representation t
    b.groupEquiv b.linearEquiv b.intertwines
  constructor
  · intro hs
    obtain ⟨k,hk⟩ := hh.mp hs
    refine ⟨k,fun x => ?_⟩
    have he := congrArg Subtype.val (MulEquiv.congr_fun hk x)
    simpa only [normalizerMonoidHom_apply_apply_coe,MulAut.conj_apply,
      Subgroup.coe_mul,Subgroup.coe_inv] using he
  · rintro ⟨k,hk⟩
    apply hh.mpr
    refine ⟨k,MulEquiv.ext fun x => Subtype.ext ?_⟩
    simpa only [normalizerMonoidHom_apply_apply_coe,MulAut.conj_apply,
      Subgroup.coe_mul,Subgroup.coe_inv] using hk x

/-- The original terminal hypotheses supply a natural central cover and
its two-support orbit on U/Z, including the exact original conjugate span. -/
theorem terminal_nonnormal_two_seed_supports
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
      Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
        (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
        (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3)) ∧
      Module.finrank (ZMod 2) ((fixedSpace a.representation (actorImage Mc K)).comap I.subtype) ≤ 1 ∧
      Module.finrank (ZMod 2) I =
        3 + Module.finrank (ZMod 2) ((fixedSpace a.representation (actorImage Mc K)).comap I.subtype) ∧
      (Module.finrank (ZMod 2) I = 3 ∨ Module.finrank (ZMod 2) I = 4) ∧
      let c := originalSection a
      let W := c.subspacePreimage I
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      ∃ t : S,
        (∀ s : S, W.map (MulAut.conj (s:G)⁻¹).toMonoidHom = W ∨
          W.map (MulAut.conj (s:G)⁻¹).toMonoidHom = W.map (MulAut.conj (t:G)⁻¹).toMonoidHom) ∧
        conjugateSpanBy W S = W ⊔ W.map (MulAut.conj (t:G)⁻¹).toMonoidHom ∧
        Module.finrank (ZMod 2) (c.imageSpace (conjugateSpanBy W S)) ≤ 8 ∧
        ∀ s : S, (s:G) ∈ normalizer (W : Set G) ↔
          ∃ k : actorImage Mc K, ∀ x : actorImage Mc K,
            let q := QuotientGroup.mk' (pCore 2 Mc)
              ⟨s,(terminal_outside hG T hempty hM hunique hmany hcard e).1.2 s.property.1⟩
            q * x.val * q⁻¹ = k.val * x.val * k.val⁻¹ := by
  obtain ⟨hU,a,I,hI,hmark,hker,hdim,halt,_⟩ := terminal_nonnormal_central_natural_support
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  obtain ⟨t,ht,hspan,hbound⟩ := source_seed_two_conjugates T Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK a hI
    (Classical.choice hmark).groupEquiv (by omega)
  exact ⟨hU,a,I,hI,hmark,hker,hdim,halt,t,ht,hspan,hbound,
    source_seed_normalizer_iff_inner T Mc
      (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK a hI
      (Classical.choice hmark)⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
