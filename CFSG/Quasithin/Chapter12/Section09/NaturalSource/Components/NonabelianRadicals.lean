module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianOrthogonalGeometry
public import Theory.Representation.BinaryIsometryRadicals
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple

/-!
# Parabolic radical comparisons in the orthogonal branch of 12.9.4

The original conjugate center moves the centralizer hyperplane into the
marked line. The faithful isometry kernels therefore put its nontrivial
dotted image in both literal parabolic two-cores. The point residual and
the full quotient Sylow exhaust the stabilizer of the seed three-space:
its index is fifteen and its order is 1344. This follows from the original
L₃(2) quotient, the full Sylow, and the faithful coset-action bound in A₈.

Conjugation followed by the original dotted projection identifies the
conjugate-center image with Z(U) modulo the center intersection and V₁.
This proves the symmetry comparison needed after the remaining order-four
and irreducibility calculation. That calculation, the minimal-parabolic
contradiction, and catalogue exhaustion remain source obligations.

Source: Aschbacher--Smith, 12.8.10(4,6) and 12.9.4,
printed pp.854,859--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
open Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The original conjugate center moves the hyperplane only into the marked plane modulo Z(U). -/
theorem nonabelian_center_hyperplane_commutator {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ⁅F.W,conjugate F.ZU g⁆ ≤ F.ZU ⊔ F.Vi 2 := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let := nonabelian_hat_elementary h earlier F hne
  have hn : 2 ≤ n := by have := h.rank; omega
  have hj := h.point_mem_Hz F earlier.alternatives
  have htwo := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) hj
  have hphi := F.localKernel_frattini_eq_point h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives) hne
  have hc := (F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)).1
  let B := F.localKernel_markedForm (by omega) htwo hphi hc
  exact F.center_commutator_le_plane hn L h.chosen.normalizes
    (F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne)
    hc (F.plane_centralizer_center B) g hgP hgH

/-- The original commutator statement on the literal faithful central quotient. -/
theorem nonabelian_center_hyperplane_displacement {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∀ a ∈ F.terminalDot (conjugate F.ZU g), ∀ w ∈ hatSpace F F.W,
      F.terminalRepresentation a w - w ∈ hatSpace F (F.Vi 2) := by
  have hc := nonabelian_center_hyperplane_commutator h earlier F hne g hgP hgH
  rw [commutator_comm,sup_comm] at hc
  rintro _ ⟨a,ha,rfl⟩ w hw
  obtain ⟨b,hb,he⟩ := (show w.toMul ∈ hatImage F F.W from hw)
  have hw' : w = hatElement F b := (congrArg Additive.ofMul he).symm
  subst w
  let au := F.U.normalizerMonoidHom
    ⟨a,le_normalizer_conjugateSpanBy V F.H a.property⟩
  let c : F.U := au b / b
  have hc' : (c:G) ∈ F.Vi 2 ⊔ F.ZU := by
    change (a:G) * (b:G) * (a:G)⁻¹ / (b:G) ∈ F.Vi 2 ⊔ F.ZU
    simpa only [commutatorElement_def,div_eq_mul_inv] using
      hc (commutator_mem_commutator (show (a:G) ∈ conjugate F.ZU g from ha)
        (show (b:G) ∈ F.W from hb))
  have hm := (mem_hatImage_mk_iff F (F.Vi 2)
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) c).mpr hc'
  change (F.terminalRepresentation _ _ - _).toMul ∈ hatImage F (F.Vi 2)
  rw [toMul_sub,F.terminalRepresentation_apply_mk]
  change F.terminalHatAction a (QuotientGroup.mk' (center F.U) b) /
    QuotientGroup.mk' (center F.U) b ∈ hatImage F (F.Vi 2)
  rw [F.terminalHatAction_apply_mk]
  simpa only [c,au,map_div] using hm

omit [Finite G] in
private theorem seed_stabilizer (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (A : Subgroup G) (hA : A ≤ normalizer (V : Set G)) :
    F.terminalDot A ≤ subspaceStabilizer F.terminalRepresentation (hatSpace F V) := by
  apply le_subspaceStabilizer
  rintro _ ⟨a,ha,rfl⟩ w hw
  obtain ⟨b,hb,he⟩ := (show w.toMul ∈ hatImage F V from hw)
  change (F.terminalRepresentation _ w).toMul ∈ hatImage F V
  refine ⟨F.uAction a b,?_,?_⟩
  · exact (mem_normalizer_iff.mp (hA ha) b).mp hb
  · rw [F.terminalRepresentation_apply_mk,←he,F.terminalHatAction_apply_mk]
    rfl

/-- The actual conjugate center lies in both parabolic two-cores appearing
in 12.9.4. The point and both cores use the unchanged faithful quotient. -/
theorem nonabelian_caseFive_center_le_twoCores
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    ∃ v : Additive F.Uhat, v ≠ 0 ∧
      hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
      F.terminalDot (conjugate F.ZU g) ≠ ⊥ ∧
      F.terminalDot (conjugate F.ZU g) ≤
        (F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))).pCoreIn 2 ⊓
          (F.terminalPointCentralizer v).pCoreIn 2 := by
  obtain ⟨hX,B,v,hB,hAlt,hInv,hv,hline,hXT,hiso,htrans,hfull,hfixed,hWX,hperp,hrank⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  let := hX
  obtain ⟨hn4,he,hd⟩ := nonabelian_caseFive_seed_intersection h hn earlier F hne g hgP hgH B₀ h5
  have hs : hatSpace F V = B.orthogonal (hatSpace F V) := by
    have hl : hatSpace F V ≤ B.orthogonal (hatSpace F V) := by
      intro a ha b hb
      exact hiso b (he.symm ▸ hb) a (he.symm ▸ ha)
    apply Submodule.eq_of_le_of_finrank_eq hl
    have hdim : finrank (ZMod 2) (hatSpace F V) = 3 := he ▸ hd
    rw [LinearMap.BilinForm.finrank_orthogonal hB,h5.1,hdim]
  have hDK : F.terminalDot (conjugate F.ZU g) ≤
      subspaceKernel F.terminalRepresentation (hatSpace F V)
        (F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))) := by
    intro a ha
    refine ⟨?_,?_⟩
    · exact (map_mono (comap_mono ((F.conjugate_ZU_le_X g).trans (hXT.trans le_sup_right)))) ha
    · intro w hw
      exact nonabelian_caseFive_center_fixes_intersection h hn earlier F hne g hgP hgH B₀ h5
        a ha w (he.symm ▸ hw)
  have hseed := BinaryIsometryRadicals.halfSpace_kernel_le_pCoreIn
    F.terminalRepresentation F.terminalRepresentation_injective B hInv (hatSpace F V) hs
    (F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G)))
    (seed_stabilizer F _ (sup_le
      (((F.Li_le L 1).trans inf_le_left).trans h.chosen.normalizes)
      (h.sylow_normalizes_seed earlier.structural)))
  have hDP : F.terminalDot (conjugate F.ZU g) ≤ F.terminalPointCentralizer v := by
    intro a ha
    exact nonabelian_caseFive_center_fixes_intersection h hn earlier F hne g hgP hgH B₀ h5
      a ha v v.property
  have hpoint := BinaryIsometryRadicals.le_pointCore_of_displacement
    F.terminalRepresentation F.terminalRepresentation_injective B hInv (v : Additive F.Uhat)
    (F.terminalPointCentralizer v) (F.terminalDot (conjugate F.ZU g)) (fun _ hx => hx) hDP
    (by
      intro a ha w hw
      rw [←hline]
      apply nonabelian_center_hyperplane_displacement h earlier F hne g hgP hgH a ha
      rwa [hperp])
  exact ⟨v,hv,hline,(nonabelian_caseFive_center h hn earlier F hne g hgP hgH B₀ h5).2,
    le_inf (hDK.trans hseed) hpoint⟩

/-- The actual center intersection and the kernel of its conjugate on U/Z(U). -/
theorem nonabelian_center_intersection_and_kernel {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.ZU ⊓ conjugate F.ZU g = Section08.centerIn (F.I₂ L) ∧
      conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype =
        Section08.centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  have hn : 2 ≤ n := by have := h.rank; omega
  have hj := h.point_mem_Hz F earlier.alternatives
  have htwo := F.localKernel_UH_isPGroup h.source.simpleQTKE L _ F.H hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) hj
  have hphi := F.localKernel_frattini_eq_point h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives) hne
  obtain ⟨hc,hs⟩ := F.localKernel_commutator_squares h.source.simpleQTKE L _ hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape F earlier.alternatives)
  have hspan := F.U_eq_plane_span L hn h.chosen.normalizes
    (F.localKernel_irreducible L hn h.chosen.normalizes (fun _ => ⟨h.naturalMarking⟩))
  have hcore := F.localKernel_eq_pCore h.source.simpleQTKE L _ F.H hn
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes earlier.structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) rfl
    (h.maximal_unique earlier.structural earlier.uniqueness).2
    (h.seed_centralizer_le earlier.structural earlier.uniqueness) h.centralizer_L hj
  let B := F.localKernel_markedForm (by omega) htwo hphi hc
  have hh := F.binary_source_center_calculations hn L h.chosen.normalizes
    ((pResidual_eq_top_iff 2 L).mp h.residual) (h.sylow_normalizes earlier.structural)
    (h.binarySeedAction_surjective F) (fun _ => h.full_L_action)
    (h.centralizer_LT earlier.structural)
    (F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne)
    hc hs hspan hne g hgP hgH hcore B
  obtain ⟨_,hcI,_,_,_,h1,h2,h3,h4,h5,_⟩ := hh
  exact ⟨hcI,h1.trans (h2.trans (h3.trans (h4.trans h5)))⟩

/-- The symmetry step in 12.9.4 retains the original conjugation map:
the conjugate-center image is the center modulo its intersection with the
conjugate center and the marked point. -/
theorem nonabelian_center_image_quotient
    {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Nonempty ((F.ZU ⧸ ((F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1).subgroupOf F.ZU) ≃*
      F.terminalDot (conjugate F.ZU g)) := by
  obtain ⟨hcI,hk⟩ := nonabelian_center_intersection_and_kernel h earlier F hne g hgP hgH
  have hg2 := F.P_le_G₂ (by have := h.rank; omega) L h.chosen.normalizes hgP
  have hDH := (F.conjugate_ZU_le_X g).trans (F.X_le_H g hg2)
  let A := (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1
  have hAg : conjugate A g = Section08.centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g := by
    change conjugate ((F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1) g = _
    rw [hcI,conjugate,Subgroup.map_sup]
    congr 1
    change conjugate (Section08.centerIn (F.I₂ L)) g = Section08.centerIn (F.I₂ L)
    rw [←centerIn_conjugate,(conjugate_eq_iff (F.I₂ L) g).mpr
      (le_normalizer_conjugateSpanBy F.U (F.P L) hgP)]
  let c : F.ZU ≃* conjugate F.ZU g := (MulAut.conj g⁻¹).subgroupMap F.ZU
  let f : F.ZU →* F.terminalDot (conjugate F.ZU g) :=
    (dotMap F F.terminalHatAction (conjugate F.ZU g) hDH).comp c.toMonoidHom
  have hk' : f.ker = A.subgroupOf F.ZU := by
    ext z
    change f z = 1 ↔ (z:G) ∈ A
    constructor
    · intro hz
      have hq := congrArg Subtype.val hz
      have ha : (inclusion hDH (c z) : F.H) ∈ F.terminalHatAction.ker :=
        (QuotientGroup.eq_one_iff _).mp hq
      have hx : (MulAut.conj g⁻¹) (z:G) ∈ conjugate A g := by
        rw [hAg,←hk]
        exact ⟨mem_map_of_mem _ z.property,mem_map_of_mem F.H.subtype ha⟩
      obtain ⟨a,ha,he⟩ := hx
      exact (MulAut.conj g⁻¹).injective he ▸ ha
    · intro hz
      have hx : (MulAut.conj g⁻¹) (z:G) ∈
          conjugate F.ZU g ⊓ F.terminalHatAction.ker.map F.H.subtype := by
        rw [hk,←hAg]
        exact mem_map_of_mem _ hz
      obtain ⟨a,ha,he⟩ := hx.2
      have he' : a = inclusion hDH (c z) := Subtype.ext he
      apply Subtype.ext
      apply (QuotientGroup.eq_one_iff _).mpr
      exact he' ▸ ha
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk'.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f
      ((dotMap_surjective F F.terminalHatAction (conjugate F.ZU g) hDH).comp c.surjective))⟩

/-- The actual quotient in the source's symmetry equation has the same
order as the dotted conjugate center. -/
theorem nonabelian_center_quotient_card
    {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Nat.card (F.ZU ⧸ ((F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1).subgroupOf F.ZU) =
      Nat.card (F.terminalDot (conjugate F.ZU g)) :=
  Nat.card_congr (nonabelian_center_image_quotient h earlier F hne g hgP hgH).some.toEquiv

private theorem index_fifteen_of_simple_order
    {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hc : Nat.card D = 20160) (P : Subgroup D)
    (hP : P ≠ ⊤) (h64 : 64 ∣ Nat.card P) (h168 : 168 ∣ Nat.card P) :
    P.index = 15 := by
  have hd : 1344 ∣ Nat.card P := by
    have hh := Nat.lcm_dvd h64 h168
    norm_num at hh
    exact hh
  obtain ⟨k,hk⟩ := hd
  have hh := P.card_mul_index
  rw [hk,mul_assoc,hc] at hh
  have he : k * P.index = 15 := Nat.eq_of_mul_eq_mul_left (by decide : 0 < 1344) hh
  have hi : P.index ∣ 15 := ⟨k,by rw [←he,Nat.mul_comm]⟩
  have hlo : 8 ≤ P.index := by
    by_contra hn
    apply hP
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hf := Nat.factorial_le (by omega : P.index ≤ 7)
    rw [hc]
    norm_num [Nat.factorial] at hf
    omega
  have hup := Nat.le_of_dvd (by decide : 0 < 15) hi
  interval_cases P.index <;> omega

/-- The original point residual and the full quotient Sylow exhaust the
stabilizer of the seed three-space. This is the end-node parabolic of
index fifteen in the original A₈ action. -/
theorem nonabelian_caseFive_seed_stabilizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G)) =
      subspaceStabilizer F.terminalRepresentation (hatSpace F V) ∧
      (F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))).index = 15 := by
  obtain ⟨e⟩ := nonabelian_caseFive_alternating_eight h hn earlier F hne B₀ h5
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup F.TerminalHdot := e.isSimpleGroup
  have hcard : Nat.card F.TerminalHdot = 20160 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.card_fin,Nat.factorial]
  let P := F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))
  let S := subspaceStabilizer F.terminalRepresentation (hatSpace F V)
  have hPS : P ≤ S := seed_stabilizer F _ (sup_le
    (((F.Li_le L 1).trans inf_le_left).trans h.chosen.normalizes)
    (h.sylow_normalizes_seed earlier.structural))
  have hSne : S ≠ ⊤ := by
    intro ht
    obtain ⟨hX,B,v,hg10,hline,_⟩ := nonabelian_g10_hypothesis h earlier F hne g hgP hgH
    let := hX
    obtain ⟨_,he,hd⟩ := nonabelian_caseFive_seed_intersection h hn earlier F hne g hgP hgH B₀ h5
    have hv : v ∈ hatSpace F V := he ▸ hg10.point_mem
    have hall : Submodule.span (ZMod 2) {w | ∃ a : F.TerminalHdot,
        F.terminalRepresentation a v = w} ≤ hatSpace F V := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,rfl⟩
      exact ((show a ∈ S from ht.symm ▸ mem_top a) v).mpr hv
    rw [hg10.orbit_span] at hall
    have heq := top_unique hall
    have hh : finrank (ZMod 2) (hatSpace F V) = 3 := he ▸ hd
    rw [heq,finrank_top,h5.1] at hh
    omega
  let Q := (T.subtype (F.invariant 1)).mapSurjective
    (f := QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  have hQP : (Q : Subgroup F.TerminalHdot) ≤ P := map_mono (comap_mono le_sup_right)
  have hQcard : Nat.card Q = 64 := by
    rw [Q.card_eq_multiplicity,hcard,show 20160 = 2^6*315 from rfl,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]
  have h64 : 64 ∣ Nat.card P := hQcard ▸ card_dvd_of_le hQP
  have hdegree := (nonabelian_caseFive_seed_intersection h hn earlier F hne g hgP hgH B₀ h5).1
  have hquot := point_hat_core_card h hn F hne
  rw [if_pos hdegree] at hquot
  have h168 : 168 ∣ Nat.card P := by
    have hd : Nat.card (F.terminalDot (F.Li L 1) ⧸ pCore 2 (F.terminalDot (F.Li L 1))) ∣
        Nat.card (F.terminalDot (F.Li L 1)) := (pCore 2 (F.terminalDot (F.Li L 1))).index_dvd_card
    rw [hquot] at hd
    exact hd.trans (card_dvd_of_le (show F.terminalDot (F.Li L 1) ≤ P from
      map_mono (comap_mono le_sup_left)))
  have hPi := index_fifteen_of_simple_order hcard P (fun he => hSne (top_unique (he ▸ hPS))) h64 h168
  have hSi := index_fifteen_of_simple_order hcard S hSne
    (h64.trans (card_dvd_of_le hPS)) (h168.trans (card_dvd_of_le hPS))
  refine ⟨eq_of_le_of_card_ge hPS ?_,hPi⟩
  have hp := P.card_mul_index
  have hs := S.card_mul_index
  rw [hPi] at hp
  rw [hSi] at hs
  dsimp only [P,S] at hp hs ⊢
  omega

/-- The literal end-node parabolic has order 1344. This fixes the group
in which the remaining two-core intersection calculation takes place. -/
theorem nonabelian_caseFive_seed_stabilizer_card
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B₀ : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B₀) :
    Nat.card (F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))) = 1344 := by
  have hi := (nonabelian_caseFive_seed_stabilizer h hn earlier F hne g hgP hgH B₀ h5).2
  obtain ⟨e⟩ := nonabelian_caseFive_alternating_eight h hn earlier F hne B₀ h5
  have hcard : Nat.card F.TerminalHdot = 20160 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.card_fin,Nat.factorial]
  have hh := (F.terminalDot (F.Li L 1 ⊔ (T : Subgroup G))).card_mul_index
  rw [hi,hcard] at hh
  omega

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
