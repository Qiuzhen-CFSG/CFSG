module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryReconstruction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeWhole
/-!
# The literal two-natural-layer reduction for larger-field SL3

The chief budget bounds the noncentral length by two. Vanishing H1 removes
all central factors on the fully moved module, so the first nonzero term and
its actual quotient are single natural modules. No common marking is assumed.

B.4.9 on a genuine DoubleNatural extension supplies an invariant complement
and same-orientation quotient identification, giving explicit two-copy
coordinates. The final source bridge constructs the faithful fully moved
component action, its offender and original failure of Irr+, so the chief
reduction can be applied without assuming G=L or an ambient splitting.

Source: Aschbacher--Smith B.5.1, printed p.101, assertions (a)--(c) and the
larger-field central-factor argument; B.4.9(2), printed pp.94--95.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups ENNReal BigOperators
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- B.4.9 supplies actual two-copy coordinates with one common marking. -/
theorem doubleNatural_three_repeated [FiniteDimensional (ZMod 2) V]
    {F : BinaryField} (D : NaturalExtensions.DoubleNatural F 3 ρ)
    (hff : IsFFModule ρ) : IsRepeatedLinearNatural ρ F 3 2 := by
  obtain ⟨⟨C,hC⟩,⟨eq⟩,_⟩ := doubleNatural_three_ff D hff
  let ec : C.toSubmodule ≃ₗ[ZMod 2] (V ⧸ D.space.toSubmodule) :=
    (Submodule.quotientEquivOfIsCompl _ _ hC).symm
  let b : C.toRepresentation.Equiv D.space.toRepresentation :=
    (Representation.Equiv.mk ec (by intro g; apply LinearMap.ext; intro v; rfl)).trans eq
  let p : (D.space.toRepresentation.prod C.toRepresentation).Equiv ρ :=
    .mk (Submodule.prodEquivOfIsCompl _ _ hC) (by
      intro g; apply LinearMap.ext; intro v
      change ρ g v.1.val + ρ g v.2.val = ρ g (v.1.val+v.2.val)
      exact (map_add _ _ _).symm)
  let q : (D.space.toSubmodule × C.toSubmodule) ≃ₗ[ZMod 2]
      ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)) :=
    D.natural.linearEquiv.prodCongr (b.toLinearEquiv.trans D.natural.linearEquiv)
  let z : ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)) ≃ₗ[ZMod 2]
      (Fin 2 → Fin 3 → F.Carrier) := (LinearEquiv.finTwoArrow (R := ZMod 2) (M := Fin 3 → F.Carrier)).symm
  refine ⟨⟨D.natural.groupEquiv,(p.symm.toLinearEquiv.trans q).trans z,?_⟩⟩
  intro g v
  have hp := LinearMap.congr_fun (p.symm.isIntertwining' g) v
  change p.symm (ρ g v) = (D.space.toRepresentation.prod C.toRepresentation) g (p.symm v) at hp
  change z (q (p.symm (ρ g v))) = _
  rw [hp]
  apply (LinearEquiv.finTwoArrow (R := ZMod 2) (M := Fin 3 → F.Carrier)).injective
  apply Prod.ext
  · exact D.natural.intertwines g (p.symm v).1
  · exact (congrArg D.natural.linearEquiv (LinearMap.congr_fun (b.isIntertwining' g) (p.symm v).2)).trans
      (D.natural.intertwines g (b (p.symm v).2))

/-- Remove the zero denominator of the first actual natural chief factor. -/
theorem first_chief_linearNatural (C : Subgroup G) (f : ReducibleChiefFlag ρ C)
    (F : BinaryField) {d : ℕ}
    (hn : IsLinearNatural ((sectionRepresentation ρ (f.chain 0) (f.chain 1)).comp C.subtype) F d) :
    IsLinearNatural ((f.chain 1).toRepresentation.comp C.subtype) F d := by
  obtain ⟨e⟩ := hn
  have hz : (sectionLower ρ (f.chain 0) (f.chain 1)).toSubmodule = ⊥ := by
    rw [f.bottom]
    change (⊥ : Submodule (ZMod 2) V).comap (f.chain 1).toSubmodule.subtype = ⊥
    rw [Submodule.comap_bot]
    exact LinearMap.ker_eq_bot.mpr (f.chain 1).toSubmodule.subtype_injective
  let q := (sectionLower ρ (f.chain 0) (f.chain 1)).toSubmodule.quotEquivOfEqBot hz
  exact ⟨⟨e.groupEquiv,q.symm.trans e.linearEquiv,fun g v => e.intertwines g (q.symm v)⟩⟩

/-- The pure SL3 chief flag has exactly two factors. -/
theorem linearThree_pure_flag_length [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hindices : f.noncentral = Finset.range f.length) : f.length = 2 := by
  classical
  have hb := f.estimates ρ hf inferInstance hcore A hA
  have hlo (i : ℕ) (hi : i ∈ f.noncentral) : (1/2 : ℝ≥0∞) ≤ quadraticRatio
      (imageRepresentation (sectionRepresentation ρ (f.chain i) (f.chain (i+1)))) :=
    linearThree_flag_ratio_lower ρ hK hsemisimple h36 earlier hsq hcore hp F mark f hi
  have hs : (f.noncentral.card : ℝ≥0∞) * (1/2) ≤ 1 := by
    calc
      _ = ∑ i ∈ f.noncentral, (1/2 : ℝ≥0∞) := by simp
      _ ≤ ∑ i ∈ f.noncentral, quadraticRatio
          (imageRepresentation (sectionRepresentation ρ (f.chain i) (f.chain (i+1)))) :=
        Finset.sum_le_sum hlo
      _ ≤ 1 := hb.2.1
  have hr := ENNReal.toReal_mono (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hs
  rw [hindices,Finset.card_range] at hr
  norm_num [ENNReal.toReal_mul,ENNReal.toReal_div] at hr
  have hu : f.length ≤ 2 := by exact_mod_cast (by linarith : (f.length : ℝ) ≤ 2)
  have hm := f.multiple
  rw [hindices,Finset.card_range] at hm
  omega

/-- The top section has the literal quotient action, retaining its actor mark. -/
theorem natural_quotient_of_top_section (U : Subrepresentation ρ)
    (F : BinaryField) {d : ℕ}
    (hn : IsLinearNatural (sectionRepresentation ρ U ⊤) F d) :
    IsLinearNatural U.quotientRepresentation F d := by
  let N := sectionLower ρ U ⊤
  let t : (⊤ : Subrepresentation ρ).toSubmodule ≃ₗ[ZMod 2] V := Submodule.topEquiv
  have he : N.toSubmodule.map t.toLinearMap = U.toSubmodule :=
    Submodule.map_comap_eq_of_surjective t.surjective U.toSubmodule
  let q := Submodule.Quotient.equiv N.toSubmodule U.toSubmodule t he
  have hq : ∀ g v, q (N.quotientRepresentation g v) = U.quotientRepresentation g (q v) := by
    intro g v
    induction v using Submodule.Quotient.induction_on with
    | _ v => rfl
  obtain ⟨a⟩ := hn
  refine ⟨⟨a.groupEquiv,q.symm.trans a.linearEquiv,?_⟩⟩
  intro g v
  have he : q.symm (U.quotientRepresentation g v) = N.quotientRepresentation g (q.symm v) := by
    apply q.injective
    rw [q.apply_symm_apply,hq,q.apply_symm_apply]
  change a.linearEquiv (q.symm (U.quotientRepresentation g v)) = _
  rw [he]
  exact a.intertwines g (q.symm v)

/-- The actual large-field source flag consists of two single natural layers. -/
theorem linearThree_large_flag_layers [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (hF : 1 < F.degree) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : generalizedFitting G ⊔ A = ⊤)
    (hm : Coinvariants.ker (ρ.comp (generalizedFitting G).subtype) = ⊤) :
    generalizedFitting G = ⊤ ∧ f.length = 2 ∧
      ∃ E E' : BinaryField, IsLinearNatural (f.chain 1).toRepresentation E 3 ∧
        IsLinearNatural (f.chain 1).quotientRepresentation E' 3 := by
  have hwhole := linearThree_flag_actor_whole ρ hK hsemisimple h36 earlier hsq hf hcore hp F mark f A hA hgen
  have hindices := (linearThree_large_source_flag_pure ρ hK hsemisimple h36 earlier hsq hf hcore hp
    F hF mark f A hA hgen hm).1
  have hlen := linearThree_pure_flag_length ρ hK hsemisimple h36 earlier hsq hf hcore hp F mark f A hA hindices
  have hn := linearThree_flag_natural ρ hK hsemisimple h36 earlier hsq hf hcore hp F mark f A hA hgen
  obtain ⟨E,hE⟩ := (hn 0 (hindices ▸ Finset.mem_range.mpr (by omega))).2.2
  obtain ⟨E',⟨a'⟩⟩ := (hn 1 (hindices ▸ Finset.mem_range.mpr (by omega))).2.2
  obtain ⟨a⟩ := first_chief_linearNatural ρ _ f E hE
  let g := ((MulEquiv.subgroupCongr hwhole).trans Subgroup.topEquiv).symm
  have hN : IsLinearNatural (f.chain 1).toRepresentation E 3 :=
    ⟨⟨g.trans a.groupEquiv,a.linearEquiv,fun x v => a.intertwines (g x) v⟩⟩
  have hQ : IsLinearNatural (sectionRepresentation ρ (f.chain 1) (f.chain 2)) E' 3 :=
    ⟨⟨g.trans a'.groupEquiv,a'.linearEquiv,fun x v => a'.intertwines (g x) v⟩⟩
  have ht : f.chain 2 = ⊤ := by simpa only [hlen] using f.top
  rw [ht] at hQ
  exact ⟨hwhole,hlen,E,E',hN,natural_quotient_of_top_section ρ _ E' hQ⟩

/-- The original moved component action satisfies the full source domain. -/
theorem linearThree_component_moved_source [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) (s : MovedSection ρ L)
    (F : BinaryField) (mark : L ≃* SL(3,F.Carrier)) :
    let δ := s.space.toRepresentation.comp L.subtype
    QuasisimpleSourceHypothesis δ K ⊤ ∧ Coinvariants.ker δ = ⊤ ∧
      ¬ IsIrrPlus δ ⊤ ⊤ := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  let μ := s.space.toRepresentation
  let δ := μ.comp L.subtype
  have hf : Function.Injective δ := by
    intro x y hxy
    apply IrreducibleBranch.component_faithful h s
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ v => exact congrArg s.central.toSubmodule.mkQ (LinearMap.congr_fun hxy v)
  have hfit : generalizedFitting L = ⊤ := generalizedFitting_eq_top_of_quasisimple
  let : IsQuasisimple (generalizedFitting L) := IsQuasisimple.of_mulEquiv
    (((MulEquiv.subgroupCongr hfit).trans Subgroup.topEquiv).symm)
  have hsq : IsSQTK K (generalizedFitting L) := (IsSQTK.equiv
    ((MulEquiv.subgroupCongr hfit).trans Subgroup.topEquiv)).mpr h.sqtk
  have hcore : pCore 2 L = ⊥ := IrreducibleBranch.local_twoCore_eq_bot L L h.fitting h.twoCore le_rfl
  obtain ⟨A,hA,hAL⟩ := linearThree_component_offender ρ hK hsemisimple h36 earlier h hnot F mark
  have hff : IsFFModule δ := ⟨A.subgroupOf L,
    ((bestOffender_on_subrepresentation ρ s.space hA.1).isOffender μ).subgroupOf μ hAL⟩
  have hs := whole_source_hypothesis δ hsq hfit hcore hf hff
  have hmov : subspaceCommutator μ ⊤ L = ⊤ := moved_commutator_top ρ s
  have hm : Coinvariants.ker δ = ⊤ := (coinvariants_eq_moved μ L).trans hmov
  refine ⟨?_,hm,?_⟩
  · simpa only [hfit] using hs
  · intro hi
    let e : (⊤ : Subgroup L) ≃* L := Subgroup.topEquiv
    have hμ : IsIrrPlus μ L ⊤ := hi.of_intertwining δ μ e.toMonoidHom e.surjective
      (LinearMap.id) Function.injective_id (fun _ _ => rfl) (by simp)
    apply moved_not_irrPlus ρ h s hnot
    change IsIrrPlus μ L (subspaceCommutator μ ⊤ L)
    rwa [hmov]

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
