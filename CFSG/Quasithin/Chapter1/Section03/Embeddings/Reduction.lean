module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Statements
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.PerfectCover
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group

/-!
# Fitting and quotient reductions for the Ξ embedding theorem

The normal branch descends from the image of X in H/O₂(H), using the
actual two-residual identity in 1.3.2(5). In the remaining branch, cyclicity
of O_p and the centralization of the other odd cores give centralization
of F. Generalized-Fitting self-centralization then detects a noncentralized
ordinary component, and solvable-quotient correspondence lifts it to a
C-component with quasisimple two-core quotient.

These reductions prove neither the supercritical input nor the subsequent
outer-automorphism containment P ≤ ⟨L^T⟩. Once containment is established,
1.3.2(2) upgrades it to X ≤ ⟨L^T⟩. The last logical corollaries explicitly
consume a proved full embedding conclusion; they are not numbered source
theorems and do not discharge that missing conclusion.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of Proposition 1.3.4, pp. 509–511, and
Proposition 1.3.5 and Lemma 1.3.6, p. 512. The general self-centralization
input is the existing proved bridge in ChapterB.QuasisimpleSections.Group.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
variable {G : Type u} [Group G]

/-- The intrinsic builder requires Sylow only in XT. Its explicit residual
identity is exactly 1.3.2(5), not normality or an embedding conclusion. -/
theorem localInput_of_mem_Xi_of_residual [Finite G] {T X H₀ : Subgroup G}
    (hX : X ∈ Xi G T) (hT : IsSylowIn 2 T (X ⊔ T)) (hH : X ⊔ T ≤ H₀)
    (hres : (pResidual 2 (H₀.pCoreIn 2 ⊔ X : Subgroup G)).map
      (H₀.pCoreIn 2 ⊔ X).subtype = X)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hq : XiOddQuotient p (XiQuotient X))
    (P : Sylow p X) : LocalInput p T X ((P : Subgroup X).map X.subtype) H₀ := by
  exact ⟨Fact.out, ho, hH, (isSylowIn_iff.mp hT).1, hX.invariant, hX.perfect,
    hq, ⟨P, rfl⟩, hX.sylow_sup hq P, hX.sylow_disjoint ho P,
    hX.core_conjugates_sylow hq P, hX.pCoreIn_eq_commutator ho hq P,
    hX.normalizer_factor hT hq P, hX.normalizer_irreducible hT ho hq P,
    lemma_1_3_2_4 hX hT ho hq P, hres⟩

/-- All the intrinsic input witnesses follow from the proved five clauses of 1.3.2.
Only this specialization uses that T is Sylow in the chosen overgroup. -/
theorem localInput_of_mem_Xi [Finite G] {T X H₀ : Subgroup G}
    (hX : X ∈ Xi G T) (hT : IsSylowIn 2 T H₀) (hH : X ⊔ T ≤ H₀)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (hq : XiOddQuotient p (XiQuotient X))
    (P : Sylow p X) : LocalInput p T X ((P : Subgroup X).map X.subtype) H₀ :=
  localInput_of_mem_Xi_of_residual hX (hT.restrict le_sup_right hH) hH
    (lemma_1_3_2_5_local hX hT) ho hq P

/-- The final containment step on p.510: conjugate generation upgrades P ≤ K
to X ≤ K when the overgroup normalizes K. -/
theorem LocalInput.le_of_complement_le {p : ℕ} {T X P H₀ K : Subgroup G}
    (h : LocalInput p T X P H₀) (hPK : P ≤ K) (hHK : H₀ ≤ normalizer K) : X ≤ K := by
  rw [← h.generation]
  apply (Subgroup.closure_le (K := K)).mpr
  rintro g ⟨n, hn, a, ha, rfl⟩
  exact (mem_normalizer_iff.mp
    (hHK (h.overgroup ((show X ≤ X ⊔ T from le_sup_left) (pCoreIn_le 2 X hn)))) a).mp (hPK ha)

/-- The two-residual identity makes X normal whenever O₂(H)X is normal in H. -/
theorem LocalInput.normal_of_core_join_normal {p : ℕ} {T X P H₀ : Subgroup G}
    (h : LocalInput p T X P H₀)
    (hn : ((H₀.pCoreIn 2 ⊔ X).subgroupOf H₀).Normal) : (X.subgroupOf H₀).Normal := by
  have hh : H₀.pCoreIn 2 ⊔ X ≤ H₀ := sup_le (pCoreIn_le 2 H₀)
    (le_sup_left.trans h.overgroup)
  have hr := normal_embedded_pResidual_subgroupOf 2 hh hn
  rwa [h.residual] at hr

/-- The normal branch of the Fitting reduction lifts from H/O₂(H) to H. -/
theorem LocalInput.normal_of_quotient_normal {p : ℕ} {T X P H₀ : Subgroup G}
    (h : LocalInput p T X P H₀)
    (hn : ((X.subgroupOf H₀).map (QuotientGroup.mk' (pCore 2 H₀))).Normal) :
    (X.subgroupOf H₀).Normal := by
  let q := QuotientGroup.mk' (pCore 2 H₀)
  let _ := hn
  have he : (((X.subgroupOf H₀).map q).comap q) =
      (H₀.pCoreIn 2 ⊔ X).subgroupOf H₀ := by
    apply (map_injective H₀.subtype_injective)
    rw [comap_map_eq, QuotientGroup.ker_mk', Subgroup.map_sup,
      map_subgroupOf_eq_of_le (le_sup_left.trans h.overgroup),
      map_subgroupOf_eq_of_le (sup_le (pCoreIn_le 2 H₀)
        (le_sup_left.trans h.overgroup))]
    exact sup_comm _ _
  apply h.normal_of_core_join_normal
  rw [← he]
  infer_instance

/-- An ordinary component is a C-component: a smaller perfect subnormal
subgroup would centralize it and hence would be trivial. -/
theorem component_isCComponent {L₀ : Subgroup G} (hL : IsComponent G L₀) :
    L₀.IsCComponent := by
  let _ := hL.2
  let _ := hL.2.simple
  have hnt : Nontrivial L₀ := (QuotientGroup.mk'_surjective (center L₀)).nontrivial
  refine ⟨(nontrivial_iff_ne_bot L₀).mp hnt, inferInstance, hL.1, ?_⟩
  intro K hK hne hp hs
  rcases hL.subnormal_dichotomy K hs with h | hc
  · exact h
  · exact (hne (bot_unique ((isPerfect_iff.mp hp).symm.le.trans
      ((commutator_mono hK le_rfl).trans hc.le)))).elim

/-- The centralizer of F* is normal abelian and is therefore contained in F. -/
theorem centralizer_generalizedFitting_le_fitting [Finite G] :
    centralizer (generalizedFitting G : Set G) ≤ fittingSubgroup G := by
  let C := centralizer (generalizedFitting G : Set G)
  have hc : C ≤ generalizedFitting G :=
    ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
  let _ : IsMulCommutative C := ⟨⟨fun x y => Subtype.ext
    ((mem_centralizer_iff.mp x.property) y (hc y.property)).symm⟩⟩
  let _ : CommGroup C := { (inferInstance : Group C) with
    mul_comm := fun x y => mul_comm' x y }
  exact le_sSup ⟨inferInstance, inferInstance⟩

/-- After centralizing F, the small Fitting intersection bounds the
centralizer of the layer by the Frattini subgroup, as on p.510. -/
theorem centralizer_layer_le_frattini [Finite G] (P : Subgroup G)
    (hPF : P ≤ centralizer (fittingSubgroup G : Set G))
    (hsmall : P ⊓ fittingSubgroup G ≤ (frattini P).map P.subtype) :
    P ⊓ centralizer (componentLayer G : Set G) ≤ (frattini P).map P.subtype := by
  apply le_trans (le_inf inf_le_left ?_) hsmall
  apply le_trans ?_ centralizer_generalizedFitting_le_fitting
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp (inf_le_left.trans hPF))
    (le_centralizer_iff.mp inf_le_right)

/-- A subgroup centralizing F but not lying in F must act nontrivially
on some ordinary component. -/
theorem exists_component_not_centralized [Finite G] (P : Subgroup G)
    (hPF : P ≤ centralizer (fittingSubgroup G : Set G))
    (hnot : ¬ P ≤ fittingSubgroup G) :
    ∃ L₀ : Subgroup G, IsComponent G L₀ ∧ ⁅L₀, P⁆ ≠ ⊥ := by
  by_contra! hn
  have he : componentLayer G ≤ centralizer (P : Set G) :=
    sSup_le fun L₀ hL => commutator_eq_bot_iff_le_centralizer.mp (hn L₀ hL)
  have hc : P ≤ centralizer (generalizedFitting G : Set G) :=
    le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hPF) he)
  exact hnot (hc.trans centralizer_generalizedFitting_le_fitting)

/-- Lift the noncentralized component through the solvable two-core,
retaining its actual image, quasisimple quotient and nontrivial commutator. -/
theorem lift_noncentralized_component [Finite G] (P : Subgroup G)
    {Lbar : Subgroup (G ⧸ pCore 2 G)} (hLbar : IsComponent (G ⧸ pCore 2 G) Lbar)
    (hn : ⁅Lbar, P.map (QuotientGroup.mk' (pCore 2 G))⁆ ≠ ⊥) :
    ∃ L₀ : Subgroup G, L₀.IsCComponent ∧ IsQuasisimple (XiQuotient L₀) ∧
      L₀.map (QuotientGroup.mk' (pCore 2 G)) = Lbar ∧ ¬ ⁅L₀, P⁆ ≤ pCore 2 G := by
  let _ := pCore_isNilpotent (p := 2) (G := G)
  obtain ⟨L₀, hL, he⟩ := (component_isCComponent hLbar).exists_map_quotient_eq (pCore 2 G)
  let _ := hLbar.2
  have eqv : XiQuotient L₀ ≃* Lbar :=
    (cComponentTwoCoreQuotientEquiv hL).trans (MulEquiv.subgroupCongr he)
  refine ⟨L₀, hL, IsQuasisimple.of_mulEquiv eqv.symm, he, ?_⟩
  intro hc
  apply hn
  rw [← he, ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hc


/-- A commutator-generated subgroup acts trivially on a normal cyclic group,
since the automorphism group of a cyclic group is abelian. -/
theorem centralizes_cyclic_normal_of_commutator (P S R : Subgroup G) [R.Normal]
    [IsCyclic R] (hP : P = ⁅P, S⁆) : P ≤ centralizer (R : Set G) := by
  let e := IsCyclic.mulAutMulEquiv R
  let _ : IsMulCommutative (MulAut R) := .of_comm fun a b =>
    e.injective (by simp only [map_mul]; exact mul_comm _ _)
  let f : G →* normalizer (R : Set G) :=
    (inclusion (show (⊤ : Subgroup G) ≤ normalizer R from le_normalizer_of_normal)).comp
      topEquiv.symm.toMonoidHom
  let ρ : G →* MulAut R := R.normalizerMonoidHom.comp f
  have hc : ⁅P, S⁆ ≤ ρ.ker := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change ρ ⁅x, y⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm' _ _)
  intro x hx
  have hxρ : R.normalizerMonoidHom (f x) = 1 := hc (hP ▸ hx)
  have hxker : f x ∈ R.normalizerMonoidHom.ker := hxρ
  rw [normalizerMonoidHom_ker] at hxker
  exact hxker


/-- The cyclic p-core and the centralization of the other odd cores imply
centralization of F, when O₂ is trivial. -/
theorem centralizes_fitting_of_cyclic_pCore [Finite G] {p : ℕ} [Fact p.Prime]
    (P S : Subgroup G) (hcore : pCore 2 G = ⊥) [IsCyclic (pCore p G)]
    (hP : P = ⁅P, S⁆)
    (hother : ∀ r : ℕ, r.Prime → Odd r → r ≠ p →
      P ≤ centralizer (pCore r G : Set G)) :
    P ≤ centralizer (fittingSubgroup G : Set G) := by
  apply le_centralizer_iff.mpr
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun r => ?_
  have hr : r.val.val.Prime := Nat.prime_of_mem_primeFactors r.val.property
  by_cases htwo : r.val.val = 2
  · rw [htwo, hcore]
    exact bot_le
  · apply le_centralizer_iff.mp
    by_cases he : r.val.val = p
    · subst p
      exact centralizes_cyclic_normal_of_commutator P S _ hP
    · exact hother r.val.val hr (Nat.odd_iff.mpr (hr.eq_two_or_odd.resolve_left htwo)) he


/-- The chosen complement is identified with X/O₂(X) by the actual quotient map. -/
noncomputable def LocalInput.complementQuotientEquiv {p : ℕ} {T X P H₀ : Subgroup G}
    (h : LocalInput p T X P H₀) : P ≃* XiQuotient X := by
  have hPX : P ≤ X := le_sup_right.trans h.complement.le
  let R := P.subgroupOf X
  let q := QuotientGroup.mk' (pCore 2 X)
  let f : R →* XiQuotient X := q.comp R.subtype
  have hgen : pCore 2 X ⊔ R = ⊤ := by
    apply map_injective X.subtype_injective
    simpa only [R, pCoreIn, Subgroup.map_sup, map_subgroupOf_eq_of_le hPX,
      ← MonoidHom.range_eq_map, range_subtype] using h.complement
  have hbij : Function.Bijective f := by
    constructor
    · apply (MonoidHom.ker_eq_bot_iff f).mp
      apply bot_unique
      intro a ha
      have hc : (a : X) ∈ pCore 2 X := (QuotientGroup.eq_one_iff _).mp ha
      have hbot := h.disjoint.le_bot ⟨mem_map_of_mem X.subtype hc, a.property⟩
      exact Subtype.ext (Subtype.ext hbot)
    · apply MonoidHom.range_eq_top.mp
      have hm := congrArg (fun A : Subgroup X => A.map q) hgen
      simpa [f, q, Subgroup.map_sup, MonoidHom.range_comp, range_subtype,
        map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using hm
  exact (subgroupOfEquivOfLe hPX).symm.trans (MulEquiv.ofBijective f hbij)


/-- The chosen complement has exactly the two odd-group alternatives of Ξ. -/
theorem LocalInput.odd_complement {p : ℕ} {T X P H₀ : Subgroup G}
    (h : LocalInput p T X P H₀) : XiOddQuotient p P :=
  h.quotient.of_mulEquiv h.complementQuotientEquiv.symm


/-- The complement in the intrinsic input is noncyclic. -/
theorem LocalInput.complement_not_cyclic [Finite G] {p : ℕ} {T X P H₀ : Subgroup G}
    (h : LocalInput p T X P H₀) : ¬ IsCyclic P := by
  let _ : Fact p.Prime := ⟨h.prime⟩
  exact h.odd_complement.not_isCyclic


/-- The actual model E_(p²) has order p². -/
theorem plane_card (p : ℕ) : Nat.card (Plane p) = p ^ 2 := by
  change Nat.card (Fin 2 → ZMod p) = p ^ 2
  simp [Nat.card_fun]


/-- The deduction in 1.3.5 from a proved 1.3.4 conclusion, using the genuine
1.2.6. This does not assert the missing embedding theorem. -/
theorem normal_of_XiStar_of_conclusion (T : Sylow 2 G) {p : ℕ} {X P H₀ : Subgroup G}
    (hX : X ∈ XiStar G (T : Subgroup G))
    (hH : H₀ ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G))
    (h : Conclusion p (T : Subgroup G) X P H₀) : (X.subgroupOf H₀).Normal := by
  rcases h with hn | ⟨L₀, hL, hq, hXL, _⟩
  · exact hn
  · have hHT : H₀ ∈ HOver G (T : Set G) := ⟨hH.1, show (T : Subgroup G) ≤ H₀ from le_sup_right.trans hH.2⟩
    have hLL := (lemma_1_2_6 T hHT).1 hL
    exact (hX.2 L₀ hLL.2 hq (sup_le
      (hXL.trans (componentOrbit_le_sup L₀ (T : Subgroup G))) le_sup_right)).elim


/-- An extraspecial quotient rules out every embedding alternative by order.
This is the normality consequence; membership in Ξ* still needs the full 1.3.6 argument. -/
theorem normal_of_extraspecial_quotient_of_conclusion {p : ℕ} {T X P H₀ : Subgroup G}
    (h : LocalInput p T X P H₀) (hex : Nat.card (XiQuotient X) = p ^ 3)
    (hc : Conclusion p T X P H₀) : (X.subgroupOf H₀).Normal := by
  rcases hc with hn | ⟨L₀, _, _, _, ⟨⟨e⟩, _⟩⟩
  · exact hn
  · have hp3 : Nat.card P = p ^ 3 := (Nat.card_congr h.complementQuotientEquiv.toEquiv).trans hex
    have hp2 : Nat.card P = p ^ 2 := (Nat.card_congr e.toEquiv).trans (plane_card p)
    have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right h.prime.one_lt (by decide)
    omega


/-- A p-subgroup of F lies in O_p, by the normality of the Sylow subgroups of F. -/
theorem pSubgroup_le_pCore_of_le_fitting [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hp : IsPGroup p P) (hPF : P ≤ fittingSubgroup G) :
    P ≤ pCore p G := by
  have hpf : IsPGroup p (P.subgroupOf (fittingSubgroup G)) := hp.comap_subtype
  obtain ⟨S, hS⟩ := hpf.exists_le_sylow
  have hm : P ≤ (S : Subgroup (fittingSubgroup G)).map (fittingSubgroup G).subtype := by
    simpa only [map_subgroupOf_eq_of_le hPF] using
      map_mono (f := (fittingSubgroup G).subtype) hS
  exact hm.trans (Sylow.map_le_pCore inferInstance inferInstance p S)


/-- The Fitting/component deduction on p.510 after the supercritical
argument has supplied cyclicity of O_p and centralization of the other odd cores.
Those two premises remain explicit; this is not an assumed 1.3.4 alternative. -/
theorem fitting_reduction [Finite G] {p : ℕ} [Fact p.Prime]
    (P S : Subgroup G) (hp : IsPGroup p P) (hnc : ¬ IsCyclic P)
    (hcore : pCore 2 G = ⊥) [IsCyclic (pCore p G)]
    (hP : P = ⁅P, S⁆)
    (hother : ∀ r : ℕ, r.Prime → Odd r → r ≠ p →
      P ≤ centralizer (pCore r G : Set G)) :
    P ≤ centralizer (fittingSubgroup G : Set G) ∧
      ∃ L₀ : Subgroup G, IsComponent G L₀ ∧ ⁅L₀, P⁆ ≠ ⊥ := by
  have hPF := centralizes_fitting_of_cyclic_pCore P S hcore hP hother
  refine ⟨hPF, exists_component_not_centralized P hPF ?_⟩
  intro hle
  have hc := pSubgroup_le_pCore_of_le_fitting hp hle
  exact hnc (isCyclic_of_injective (inclusion hc) (inclusion_injective hc))


/-- The stronger Frattini commutator identity in 1.3.2(4) gives P = [P,N_T(P)]. -/
theorem LocalInput.complement_eq_commutator_normalizer {p : ℕ} {T X P H₀ : Subgroup G}
    (h : LocalInput p T X P H₀) : P = ⁅P, T ⊓ normalizer P⁆ := by
  apply le_antisymm
  · exact h.frattini_commutator.le.trans (commutator_mono le_rfl (map_subtype_le _))
  · exact le_normalizer_iff_commutator_le_left.mp inf_le_right

end CFSG.Quasithin.Chapter1.XiEmbedding
