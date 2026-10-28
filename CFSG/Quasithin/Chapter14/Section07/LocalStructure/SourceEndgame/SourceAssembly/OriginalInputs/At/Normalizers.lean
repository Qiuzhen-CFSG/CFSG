module
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.Source
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Intersections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Baumann
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.ThompsonSolvability
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Centralizers

/-!
# The residual normalizer and fixed centralizers at G,T

The original weak closure lies in O₂(LT): each contained conjugate of V
centralizes V, by hyperplane control and the original point commutator.
Maximal two-local uniqueness bounds its normalizer. In the solvable
Thompson branch the literal S₃ quotient supplies the second weak-closure
clause, forcing a nontrivial two-perfect subgroup into T. Together with
the proved component exclusion and natural-point Baumann bound this gives
N_G(K)=H. The original fixed-component theorem then supplies both clauses
of 14.7.68, including uniqueness among conjugates of U₀.

Only structural, faithful-family and original A₅ module results at this
G,T remain explicit, with their existing producers. Final 14.7.75 discharge
stays with qt-d-14775-source. Source: AS 14.7.31 and 14.7.67–68,
printed pp.1055,1070–1072. The universal public interfaces are preserved.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.EarlierWeakClosureAt
open Chapter12.Section08 Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem right_conjugate_mul (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
private theorem centralizer_conjugate (A : Subgroup G) (g : G) :
    centralizer (conjugate A g : Set G) = conjugate (centralizer (A : Set G)) g := by
  exact (map_centralizer_equiv (A : Set G) (MulAut.conj g⁻¹)).symm

omit [Finite G] in
private theorem normalizer_conjugate (A : Subgroup G) (g : G) :
    normalizer (conjugate A g : Set G) = conjugate (normalizer (A : Set G)) g :=
  (map_normalizer_eq_of_bijective A (MulAut.conj g⁻¹).bijective).symm

/-- Source (*) for each plane of each conjugate of the original V. -/
theorem hyperplane_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (g : G) (A : Subgroup G) (hAV : A ≤ conjugate V g) (hcard : Nat.card A = 4) :
    centralizer (A : Set G) ≤ normalizer (conjugate V g : Set G) := by
  have hne : F.Vi 2 ≠ ⊥ := by
    intro he
    have hc := F.card 2 (by decide)
    rw [he, card_bot] at hc
    norm_num at hc
  have hbase : centralizer (F.Vi 2 : Set G) ≤ normalizer (V : Set G) :=
    (le_inf hplane le_rfl).trans
      (inf_centralizer_le_normalizer_of_trivial_intersections
        ((structural L h.source).2.2 V h.chosen).2.2.1 hne (F.le_seed 2))
  have hpull : conjugate A g⁻¹ ≤ V := by
    have hm := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hAV
    change conjugate A g⁻¹ ≤ conjugate (conjugate V g) g⁻¹ at hm
    exact hm.trans_eq (by simpa only [inv_inv] using conjugate_conjugate_inv V g⁻¹)
  obtain ⟨l, hl, he⟩ := h.subspace_transitive (conjugate A g⁻¹) (F.Vi 2)
    hpull (F.le_seed 2) (by
      rw [conjugate, card_map_of_injective (MulAut.conj (g⁻¹)⁻¹).injective, hcard,
        F.card 2 (by decide)]
      norm_num)
  have hpullcentral : centralizer (conjugate A g⁻¹ : Set G) ≤ normalizer (V : Set G) := by
    have hc := map_mono (f := (MulAut.conj (l⁻¹)⁻¹).toMonoidHom) hbase
    change conjugate (centralizer (F.Vi 2 : Set G)) l⁻¹ ≤
      conjugate (normalizer (V : Set G)) l⁻¹ at hc
    rw [← centralizer_conjugate, ← normalizer_conjugate,
      (conjugate_eq_iff V l⁻¹).mpr (h.chosen.normalizes (L.inv_mem hl)),
      ← he] at hc
    have he : conjugate (conjugate (conjugate A g⁻¹) l) l⁻¹ = conjugate A g⁻¹ := by
      simpa only [inv_inv] using conjugate_conjugate_inv (conjugate A g⁻¹) l⁻¹
    rwa [he] at hc
  have hc := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hpullcentral
  change conjugate (centralizer (conjugate A g⁻¹ : Set G)) g ≤
    conjugate (normalizer (V : Set G)) g at hc
  rwa [← centralizer_conjugate, conjugate_conjugate_inv, ← normalizer_conjugate] at hc

/-- A nonzero intersection can be marked by the original flag point. -/
theorem returning_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (B : Subgroup G) (g : G)
    (hne : conjugate V g ⊓ B ≠ ⊥) :
    ∃ k : G, conjugate V k = conjugate V g ∧ conjugate (F.Vi 1) k ≤ B := by
  let := h.chosen.elementary
  obtain ⟨x, hx⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hx1 : (x : G) ≠ 1 := fun he => hx (Subtype.ext he)
  obtain ⟨v, hv, hvx⟩ := x.property.1
  have hv1 : v ≠ 1 := by
    intro he
    subst v
    exact hx1 (hvx.symm.trans (map_one _))
  have hv2 : v ^ 2 = 1 := by
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  have hcv : Nat.card (zpowers v) = Nat.card (F.Vi 1) := by
    rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1, F.card 1 (by decide), pow_one]
  obtain ⟨l, hl, he⟩ := h.subspace_transitive (F.Vi 1) (zpowers v)
    (F.le_seed 1) (zpowers_le.mpr hv) hcv.symm
  refine ⟨l * g, ?_, ?_⟩
  · rw [right_conjugate_mul, (conjugate_eq_iff V l).mpr (h.chosen.normalizes hl)]
  · rw [right_conjugate_mul, he]
    change (zpowers v).map (MulAut.conj g⁻¹).toMonoidHom ≤ B
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr (hvx.symm ▸ x.property.2)

/-- Every conjugate in the relative Sylow lies in the actual normal two-core. -/
theorem conjugate_le_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (A B : Subgroup G) (hBN : A ≤ normalizer (B : Set G))
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hcore : A ⊓ centralizer (B : Set G) = A.pCoreIn 2)
    (hreturn : ∀ g : G, conjugate (F.Vi 1) g ≤ B →
      conjugate F.U g ≤ A ⊓ centralizer (B : Set G))
    (g : G) (hg : conjugate V g ≤ A) : conjugate V g ≤ A.pCoreIn 2 := by
  let := h.chosen.elementary
  by_contra hout
  let C := conjugate V g
  have hC : IsPGroup 2 C := (IsElementaryAbelian.isPGroup 2 V).map _
  have hi := (core_hyperplane_and_generation A C hg hC hout e).1
  have hcardC : Nat.card C = 8 := by
    change Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) = 8
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, h.seed_card]
    norm_num
  have hcardD : Nat.card (C ⊓ A.pCoreIn 2 : Subgroup G) = 4 := by
    have he := ((C ⊓ A.pCoreIn 2).subgroupOf C).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C ⊓ A.pCoreIn 2 ≤ C from inf_le_left)).toEquiv] at he
    change (C ⊓ A.pCoreIn 2).relIndex C * _ = Nat.card C at he
    rw [hi, hcardC] at he
    omega
  have hBC : B ≤ normalizer (C : Set G) := by
    apply le_trans _ (hyperplane_centralizer h structural F hplane g
      (C ⊓ A.pCoreIn 2) inf_le_left hcardD)
    apply le_centralizer_iff.mpr
    exact inf_le_right.trans (hcore.symm.le.trans inf_le_right)
  have hCB : C ≤ normalizer (B : Set G) := hg.trans hBN
  have hcomm : ⁅C, B⁆ ≤ C ⊓ B :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hBC)
      (le_normalizer_iff_commutator_le_right.mp hCB)
  have hinter : C ⊓ B ≠ ⊥ := by
    intro he
    have hc : C ≤ centralizer (B : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp (he ▸ hcomm))
    exact hout (hcore ▸ le_inf hg hc)
  obtain ⟨k, hk, hp⟩ := returning_point h F B g hinter
  apply hout
  rw [← hk]
  exact (map_mono (le_conjugateSpanBy V F.H)).trans ((hreturn k hp).trans hcore.le)

/-- Clause (2), with the actual relative Sylow and corank-zero construction. -/
theorem clause_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (A R B : Subgroup G) (hSylow : Chapter1.IsSylowIn 2 R A)
    (hBA : B ≤ A) (hB : IsPReduced 2 (B.subgroupOf A))
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hcore : A ⊓ centralizer (B : Set G) = A.pCoreIn 2)
    (hreturn : ∀ g : G, conjugate (F.Vi 1) g ≤ B →
      conjugate F.U g ≤ A ⊓ centralizer (B : Set G)) :
    ChapterE.indexedWeakClosure V R 0 ≤ A ∧
      A ≤ normalizer (ChapterE.indexedWeakClosure V R 0 : Set G) := by
  obtain ⟨S, hS⟩ := hSylow
  have hRA : R ≤ A := hS ▸ map_subtype_le _
  have hW : ChapterE.indexedWeakClosure V R 0 ≤ A.pCoreIn 2 := by
    rw [ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro C hC
    obtain ⟨g, rfl, hg⟩ := (ChapterE.mem_gamma_zero_iff V R C).mp hC
    simpa only [conjugate, inv_inv] using conjugate_le_core h structural F hplane A B
      ((normal_subgroupOf_iff_le_normalizer hBA).mp hB.normal) e hcore hreturn
      g⁻¹ (by simpa only [conjugate, inv_inv] using hg.trans hRA)
  refine ⟨(ChapterE.indexedWeakClosure_le V R 0).trans hRA, ?_⟩
  have he := ChapterE.weakClosure_eq_in_two_overgroup V A S (A.pCoreIn 2) 0
    (isPGroup_pCoreIn 2 A) (pCoreIn_le 2 A) (by simpa only [hS] using hW)
  rw [hS] at he
  rw [he]
  exact (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))).trans
    (ChapterE.normalizer_le_weakClosure_normalizer V (A.pCoreIn 2) 0)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.EarlierWeakClosureAt

public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.EarlierWeakClosureAt
open Chapter12.Section08 Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- G.2.2 on L₁T, with its actual embedded two-core R₁. -/
theorem point_core_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) : ⁅V, F.Ri L 1⁆ ≤ F.Vi 1 := by
  let := h.chosen.elementary
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  have hJH : J ≤ F.H :=
    sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)
  have hc : Nat.card (F.Vi 1) = 2 := by simpa only [pow_one] using F.card 1 (by decide)
  have hp : F.Vi 1 ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    omega
  have hpJ : F.Vi 1 ≤ J := (F.le_seed 1).trans (h.chosen.le_sylow.trans le_sup_right)
  have hpQ : F.Vi 1 ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsPGroup.of_card (n := 1) (by simpa using hc)) hpJ hJH
  have hQ : J.pCoreIn 2 ≠ ⊥ := fun he => hp (le_bot_iff.mp (he ▸ hpQ))
  have hJ : J ∈ F.Hz L ⊥ := by
    refine ⟨⟨hQ, ?_⟩, hJH, ?_⟩
    · intro x hx
      rcases hx with hx | hx
      · exact mem_sup_left hx
      · exact mem_sup_right hx
    · intro he
      exact hp (le_bot_iff.mp (hpJ.trans he))
  have hs := F.localKernel_hypothesis h.source.simpleQTKE L ⊥ J (by decide)
    h.chosen.le_sylow h.chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) hJ
  have hh := hs.commutator_U_core_le_point
  change ⁅conjugateSpanBy V J, J.pCoreIn 2⁆ ≤ F.Vi 1 at hh
  exact (commutator_mono (le_conjugateSpanBy V J) le_rfl).trans hh

/-- The abelian point span forces intersecting seed conjugates to commute. -/
theorem intersecting_conjugates_commute
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (hU : IsMulCommutative F.U) (g : G)
    (hne : V ⊓ conjugate V g ≠ ⊥) : ⁅V, conjugate V g⁆ = ⊥ := by
  let := h.chosen.elementary
  have hc : Nat.card (F.Vi 1) = 2 := by simpa only [pow_one] using F.card 1 (by decide)
  have hp : F.Vi 1 ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hc
    omega
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp hp
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hzV := F.le_seed 1 z.property
  have hpoint : F.Vi 1 = zpowers (z : G) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr z.property) ?_).symm
    rw [Nat.card_zpowers, orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) hzV) hz1, hc]
  apply ((F.abelian_U_iff_intersections_commute (by decide) z hpoint hz1 ?_).mp hU) g hne
  intro x hx hx1
  obtain ⟨l, hl, he⟩ := h.vector_transitive hzV hx hz1 hx1
  exact ⟨l, h.chosen.normalizes hl, he⟩

omit [Finite G] in
/-- A central order-two displacement makes each vector centralize a hyperplane. -/
private theorem normalizes_of_point_commutator
    (C P : Subgroup G) [IsMulCommutative P]
    (hC : Nat.card C = 8) (hP : Nat.card P = 2)
    (hCP : C ≤ centralizer (P : Set G)) (v : G)
    (hcomm : ∀ c ∈ C, ⁅c, v⁆ ∈ P)
    (hhyper : ∀ D ≤ C, Nat.card D = 4 → centralizer (D : Set G) ≤ normalizer (C : Set G)) :
    v ∈ normalizer (C : Set G) := by
  let f : C →* P := {
    toFun := fun c => ⟨⁅(c : G), v⁆, hcomm c c.property⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro a b
      apply Subtype.ext
      change ⁅(a : G) * (b : G), v⁆ = ⁅(a : G), v⁆ * ⁅(b : G), v⁆
      rw [commutatorElement_mul_left_eq_conj_mul,
        ← hCP a.property _ (hcomm b b.property), mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (⟨⁅(b : G), v⁆, hcomm b b.property⟩ : P)
        (⟨⁅(a : G), v⁆, hcomm a a.property⟩ : P)) }
  let D := f.ker.map C.subtype
  have hDC : D ≤ C := map_subtype_le _
  have hvD : v ∈ centralizer (D : Set G) := by
    rintro x ⟨c, hc, rfl⟩
    have he : ⁅(c : G), v⁆ = 1 := congrArg Subtype.val (show f c = 1 from hc)
    exact commutatorElement_eq_one_iff_mul_comm.mp he
  have hidx : f.ker.index = 1 ∨ f.ker.index = 2 := by
    rw [index_ker]
    have hd := f.range.card_subgroup_dvd_card
    rw [hP] at hd
    exact (Nat.dvd_prime Nat.prime_two).mp hd
  rcases hidx with hidx | hidx
  · have hker : f.ker = ⊤ := index_eq_one.mp hidx
    have hDCeq : D = C := by simp only [D, hker, ← MonoidHom.range_eq_map, range_subtype]
    exact Subgroup.centralizer_le_normalizer _ (hDCeq ▸ hvD)
  · apply hhyper D hDC _ hvD
    have he := f.ker.index_mul_card
    rw [hidx, hC] at he
    change Nat.card (f.ker.map C.subtype) = 4
    rw [card_map_of_injective C.subtype_injective]
    omega

/-- Hyperplane control excludes every noncentral conjugate contained in R₁. -/
theorem conjugate_in_R_centralizes
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hU : IsMulCommutative F.U)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (g : G) (hg : conjugate V g ≤ F.Ri L 1) :
    conjugate V g ≤ centralizer (V : Set G) := by
  let := h.chosen.elementary
  by_cases hinter : V ⊓ conjugate V g = ⊥
  · have hRT : F.Ri L 1 ≤ (T : Subgroup G) :=
      (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
        (map_subgroupOf_eq_of_le le_sup_right)
    have hCN : conjugate V g ≤ normalizer (V : Set G) :=
      hg.trans (hRT.trans (h.sylow_normalizes_seed_at structural))
    have hCP : conjugate V g ≤ centralizer (F.Vi 1 : Set G) :=
      (hg.trans (hRT.trans (F.invariant 1))).trans
        (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
    have hdisp : ⁅conjugate V g, V⁆ ≤ F.Vi 1 := by
      rw [commutator_comm]
      exact (commutator_mono le_rfl hg).trans (point_core_commutator h structural F)
    let : IsElementaryAbelian 2 (F.Vi 1) :=
      IsElementaryAbelian.of_injective (inclusion (F.le_seed 1)) (inclusion_injective _)
    have hVN : V ≤ normalizer (conjugate V g : Set G) := by
      intro v hv
      apply normalizes_of_point_commutator (conjugate V g) (F.Vi 1)
        (by rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, h.seed_card]; norm_num)
        (by simpa using F.card 1 (by decide)) hCP v
        (fun c hc => hdisp (commutator_mem_commutator hc hv))
      exact fun D hD hc => hyperplane_centralizer h structural F hplane g D hD hc
    apply le_centralizer_iff.mpr
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [← hinter]
    exact le_inf (le_normalizer_iff_commutator_le_left.mp hCN)
      (le_normalizer_iff_commutator_le_right.mp hVN)
  · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (intersecting_conjugates_commute h F hU g hinter))

/-- Clause (1): core containment, LT-normality, and the full ambient normalizer bound. -/
theorem clause_one
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hU : IsMulCommutative F.U)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    ChapterE.indexedWeakClosure V (F.Ri L 1) 0 ≤ L ⊔ (T : Subgroup G) ∧
      L ⊔ (T : Subgroup G) ≤
        normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ∧
      normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) ≤
        normalizer (L : Set G) := by
  let := h.chosen.elementary
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hQN : L ⊔ (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)))
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow _ (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hJLT : F.Li L 1 ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) :=
    sup_le_sup_right ((F.Li_le L 1).trans inf_le_left) _
  have hQR : Q ≤ F.Ri L 1 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _) (hQT.trans le_sup_right)
      (hJLT.trans hQN)
  have hVQ : V ≤ Q := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    (h.chosen.le_sylow.trans le_sup_right)
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural))
  have hRLT : F.Ri L 1 ≤ L ⊔ (T : Subgroup G) := (pCoreIn_le 2 _).trans hJLT
  have hWC : ChapterE.indexedWeakClosure V (F.Ri L 1) 0 ≤ centralizer (V : Set G) := by
    rw [ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro C hC
    obtain ⟨g, rfl, hg⟩ := (ChapterE.mem_gamma_zero_iff V (F.Ri L 1) C).mp hC
    simpa only [conjugate, inv_inv] using conjugate_in_R_centralizes h structural F hU
      hplane g⁻¹ (by simpa only [conjugate, inv_inv] using hg)
  have hWQ : ChapterE.indexedWeakClosure V (F.Ri L 1) 0 ≤ Q :=
    (le_inf ((ChapterE.indexedWeakClosure_le _ _ _).trans hRLT) hWC).trans
      (h.centralizer_LT_at structural).le
  have heq : ChapterE.indexedWeakClosure V (F.Ri L 1) 0 =
      ChapterE.indexedWeakClosure V Q 0 :=
    le_antisymm (SubgroupFamily.span_le_span_of_span_le hWQ)
      (ChapterE.weakClosure_mono V 0 hQR)
  have hn : L ⊔ (T : Subgroup G) ≤
      normalizer (ChapterE.indexedWeakClosure V (F.Ri L 1) 0 : Set G) := by
    rw [heq]
    exact hQN.trans (ChapterE.normalizer_le_weakClosure_normalizer V Q 0)
  refine ⟨hWQ.trans (pCoreIn_le 2 _), hn, ?_⟩
  apply normalizer_le_of_unique_maximalTwoLocal (J := L ⊔ (T : Subgroup G)) _
    ((isPGroup_pCoreIn 2 _).to_le hWQ) _ hn
  · intro N hN hJN
    exact Set.mem_singleton_iff.mp ((h.maximal_unique_at structural).2 ▸
      show N ∈ {N : Subgroup G | IsMaximalTwoLocal N ∧ L ⊔ (T : Subgroup G) ≤ N}
        from ⟨hN, hJN⟩)
  · intro he
    exact h.chosen.ne_bot (le_bot_iff.mp (he ▸
      ChapterE.self_le_weakClosure_zero (hVQ.trans hQR)))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.EarlierWeakClosureAt

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Chapter12.Section08 Theory.GroupTheory ResidualNormalizer
open Chapter13.Section03.SourceCompletion
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
include d
/-- Actual application of both clauses of 14.7.31 to W₀(R₁,V). The outstanding
S₃ identification is explicit; the theorem does not certify B.2.16. -/
theorem false_of_residual_thompson_quotient_at
    (earlier : d.ModuleSeparation)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hDM : D F ⊓ normalizer (L : Set G) ≤ (T : Subgroup G))
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    (hBaum : normalizer (ChapterB.baumann (F.Ri L 1) : Set G) ≤ normalizer (L : Set G))
    (hD : ¬ IsPGroup 2 (D F))
    (e : JRQuotient L F ≃* Equiv.Perm (Fin 3)) : False := by
  have hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G) :=
    (d.plane_centralizer_le earlier).trans (d.natural.sylow_normalizes_at structural)
  have hfirst := EarlierWeakClosureAt.clause_one d.natural structural F d.abelian hplane
  have hc := d.residual_thompsonJoin_centralizer_eq_core_of_quotient hSylow e
  have hmodel : Nonempty (((JR L F) ⧸ pCore 2 (JR L F)) ≃* Equiv.Perm (Fin 3)) := by
    exact ⟨(QuotientGroup.quotientMulEquivOfEq
      (residual_thompsonJoin_core_of_quotient e).symm).trans e⟩
  have hnormal := EarlierWeakClosureAt.clause_two d.natural structural F hplane
    (JR L F) (F.Ri L 1) (E F)
    (residual_thompsonJoin_sylow hSylow)
    ((d.residualSpan_le_R hSylow).trans le_sup_right)
    (d.residual_thompsonJoin_reduced_of_quotient hSylow e) hmodel.some hc
    (fun g hg => (d.returning_point_U_le_thompsonJoin_core hSylow g hg).trans hc.symm.le)
  exact d.false_of_thompsonJoin_normalizer_bound hDM hSylow hBaum hD
    (ChapterE.indexedWeakClosure V (F.Ri L 1) 0) hnormal.2 hfirst.2.2


/-- The complete 14.7.67 normalizer identity from only original ambient inputs. -/
theorem normalizer_K_eq_H_from_original_modules_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (five : OriginalAlternatingFiveModules1332At T L) :
    normalizer (K F : Set G) = F.H ∧ IsMaximalTwoLocal F.H := by
  have hs := d.Ri_isSylowIn_D_sup_Ri
  have hDM := (d.residual_intersections_at structural).2.1
  have hBaum := d.baumann_normalizer_from_original_modules_at structural five
  have hsol := d.residual_thompson_solvable_of_original_modules_at faithful five
  have hD : IsPGroup 2 (D F) := by
    by_contra hn
    obtain ⟨e⟩ := d.residual_thompsonJoin_quotient_symmetricThree_source hsol hDM hs hBaum hn
    exact d.false_of_residual_thompson_quotient_at (Rechoice.SourceCompletion.moduleSeparation d)
      structural hDM hs hBaum hn e
  have he := d.normalizer_K_eq_H_of_sectionCentralizer_twoGroup d.normalizer_K_eq_sup_D_T hD
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S B hB
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hB
  exact ⟨he,he ▸ (d.residual_normalizer_unique faithful uniqueness).1⟩

/-- The actual fixed-component application discharges the preceding normalizer
and maximality inputs and proves both original 14.7.68 clauses. -/
theorem source_lemma_14_7_68_from_original_modules_at
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (five : OriginalAlternatingFiveModules1332At T L) :
    {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z} ∧
      ∀ u : F.U, (u : G) ∈ d.U₀ → (u : G) ≠ 1 → d.FixedModuloPoint u →
        centralizer ({(u : G)} : Set G) ≤ F.H ∧
          ∀ g : G, (u : G) ∈ conjugate d.U₀ g → conjugate d.U₀ g = d.U₀ := by
  obtain ⟨hNK,hmax⟩ := d.normalizer_K_eq_H_from_original_modules_at structural faithful five
  exact d.source_lemma_14_7_68_at five hNK hmax
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
