module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.Local

/-!
# Non-enlargement in the two surviving source rows

The remaining 14.7.49–51 exclusions remove only named component rows;
they assume neither a whole-residual alternative nor uniqueness of H_z.
After 14.7.48 the component in each original I is O²(I). Functoriality
embeds it in the actual component O²(G₁). This constructs the source
overcomponent with its literal inclusion, without a containment premise.

The two relevant A.3.12 cases admit a direct order proof. Map the smaller
component into G₁/O₂(G₁). The kernel is a two-group, so its intrinsic
core-quotient order divides the image order. The larger component image
has order 60 or 6048. Neither number divides the other; in either matching
case the image fills the larger component image. The original full Sylow
contains the quotient kernel and supplements that larger component. Thus
I = G₁, excluding strict enlargement and proving generic local uniqueness.

Source: Aschbacher–Smith, 14.7.49–52 and the corresponding A.3.12
non-enlargement cases, printed pp.1064–1065 and 47–48, refs/quasithin.pdf.
The exclusions retain qt-d-14751-inner-linear-exclusion and
qt-d-14752-local-reduction as their source producers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}


/-- The two surviving actual component quotient carriers. -/
@[expose] def ResidualRows (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* alternatingGroup (Fin 5)) ∨
    Nonempty (X ≃* commutator (Atlas.G2.Model (ZMod 2)))

/-- Only the remaining source row exclusions, on components of original locals. -/
@[expose] def RowExclusions (F : InvariantFlag T V 3) (L : Subgroup G) : Prop :=
  ∀ (I : Subgroup G), I ∈ F.Hz L (normalizer (L : Set G)) →
    ∀ (C : Subgroup I), C.IsCComponent →
      (∀ n : ℕ, 3 ≤ n → n ≤ 5 → ¬ Nonempty ((C ⧸ pCore 2 C) ≃* SL(n, ZMod 2))) ∧
      ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 6)) ∧
      ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7))

omit [Finite G] in
/-- Apply 14.7.49–51 to the intrinsic quotient of an actual component. -/
theorem local_component_residual_rows
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) : ResidualRows (C ⧸ pCore 2 C) := by
  obtain ⟨hl,h6,h7⟩ := exclusions I hI C hC
  rcases (source47 I hI C hC).2 with ⟨n,hn,hn',he⟩ | ⟨n,hn,hn',he⟩ | he
  · exact (hl n hn hn' he).elim
  · have hn'' : n = 5 ∨ n = 6 ∨ n = 7 := by omega
    rcases hn'' with rfl | rfl | rfl
    · exact Or.inl he
    · exact (h6 he).elim
    · exact (h7 he).elim
  · exact Or.inr he

/-- The exact orders needed by the two source non-enlargement cases. -/
theorem ResidualRows.card {X : Type*} [Group X] (hm : ResidualRows X) :
    Nat.card X = 60 ∨ Nat.card X = 6048 := by
  rcases hm with he | he
  all_goals obtain ⟨e⟩ := he
  · left
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  · exact Or.inr ((Nat.card_congr e.toEquiv).trans
      Atlas.G2.LieAutomorphismExtensions.card_binaryDerived)

private theorem quotient_core_card_dvd_of_two_kernel
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) :
    Nat.card (X ⧸ pCore 2 X) ∣ Nat.card Y := by
  have hker : f.ker ≤ pCore 2 X := le_sSup ⟨inferInstance,hk⟩
  let r : (X ⧸ f.ker) →* (X ⧸ pCore 2 X) := QuotientGroup.lift f.ker
    (QuotientGroup.mk' (pCore 2 X)) (by simpa only [QuotientGroup.ker_mk'] using hker)
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) x
    exact ⟨QuotientGroup.mk' f.ker x,rfl⟩
  have hd := card_dvd_of_surjective r hr
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at hd

private theorem residual_row_image_eq
    {X : Type*} [Group X] [Finite X] (Q : Subgroup X) [Q.Normal]
    (hp : IsPGroup 2 Q) (B C : Subgroup X) (hBC : B ≤ C)
    (hB : ResidualRows (B ⧸ pCore 2 B))
    (hC : ResidualRows (C.map (QuotientGroup.mk' Q))) :
    B.map (QuotientGroup.mk' Q) = C.map (QuotientGroup.mk' Q) := by
  let q := QuotientGroup.mk' Q
  let b := B.map q
  let c := C.map q
  let f := q.subgroupMap B
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = Q.comap B.subtype := by
      ext x
      change (⟨q x,_⟩ : B.map q) = 1 ↔ (x : X) ∈ Q
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff _
    rw [he]
    exact hp.comap_of_injective B.subtype B.subtype_injective
  have hd : Nat.card (B ⧸ pCore 2 B) ∣ Nat.card b :=
    quotient_core_card_dvd_of_two_kernel f (q.subgroupMap_surjective B) hk
  have hbc : b ≤ c := map_mono hBC
  have htotal := hd.trans (card_dvd_of_le hbc)
  have hecard : Nat.card (B ⧸ pCore 2 B) = Nat.card c := by
    have hcards : Nat.card c = 60 ∨ Nat.card c = 6048 := hC.card
    rcases hB.card with hb | hb <;> rcases hcards with hc | hc
    · exact hb.trans hc.symm
    · norm_num [hb,hc] at htotal
    · norm_num [hb,hc] at htotal
    · exact hb.trans hc.symm
  exact eq_of_le_of_card_ge hbc (hecard ▸ Nat.le_of_dvd Nat.card_pos hd)

/-- The literal source overcomponent comparison forces every original local to be G₁. -/
theorem local_eq_full_point_of_row_exclusions
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) : I = F.H := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  obtain ⟨C,hC,_,_⟩ := local_exists_quasisimple_component d h hab structural previous
    faithful earlier I hI
  obtain ⟨D,hD,_,_⟩ := local_exists_quasisimple_component d h hab structural previous
    faithful earlier F.H hH
  obtain ⟨hc,hcgen,_⟩ := local_component_eq_residual d h hab structural previous faithful
    earlier source47 I hI C hC
  obtain ⟨hd,hdgen,_⟩ := local_component_eq_residual d h hab structural previous faithful
    earlier source47 F.H hH D hD
  have hIH : I ≤ F.H := hI.2.1
  let j : I →* F.H := inclusion hIH
  let B := C.map j
  let q := QuotientGroup.mk' (pCore 2 F.H)
  let J := I.subgroupOf F.H
  have hBD : B ≤ D := by
    change C.map j ≤ D
    rw [←hc,←hd]
    exact map_pResidual_le 2 j
  let eB : C ≃* B := equivMapOfInjective C j (inclusion_injective hI.2.1)
  let eBQ := QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)
  have hbrow : ResidualRows (B ⧸ pCore 2 B) := by
    rcases local_component_residual_rows source47 exclusions I hI C hC with he | he
    all_goals obtain ⟨e⟩ := he
    · exact Or.inl ⟨eBQ.symm.trans e⟩
    · exact Or.inr ⟨eBQ.symm.trans e⟩
  have hdrow : ResidualRows (D.map q) := by
    rcases local_component_residual_rows source47 exclusions F.H hH D hD with he | he
    all_goals obtain ⟨e⟩ := he
    · exact Or.inl ⟨(cComponentTwoCoreQuotientEquiv hD).symm.trans e⟩
    · exact Or.inr ⟨(cComponentTwoCoreQuotientEquiv hD).symm.trans e⟩
  have he := residual_row_image_eq (pCore 2 F.H) pCore_isPGroup B D hBD hbrow hdrow
  have hBJ : B ≤ J := by
    rintro _ ⟨c,_,rfl⟩
    exact c.property
  have hDJ : D.map q ≤ J.map q := he ▸ map_mono hBJ
  let S := T.subtype (F.sylow_le_of_mem_Hz hH)
  have hSJ : (S : Subgroup F.H) ≤ J := by
    intro t ht
    exact F.sylow_le_of_mem_Hz hI ht
  have hgen : D ⊔ (S : Subgroup F.H) = ⊤ := by
    apply map_injective F.H.subtype_injective
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hH),
      ←MonoidHom.range_eq_map,range_subtype]
    exact hdgen
  have hJq : J.map q = ⊤ := by
    apply top_unique
    rw [←map_top_of_surjective q (QuotientGroup.mk'_surjective _),←hgen,Subgroup.map_sup]
    exact sup_le hDJ (map_mono hSJ)
  have hcore : pCore 2 F.H ≤ J := (pCore_isPGroup.le_sylow_of_normal S).trans hSJ
  have hJ : J = ⊤ := by
    have hh := congrArg (Subgroup.comap q) hJq
    rwa [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hcore,comap_top] at hh
  exact le_antisymm hI.2.1 (subgroupOf_eq_top.mp hJ)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
