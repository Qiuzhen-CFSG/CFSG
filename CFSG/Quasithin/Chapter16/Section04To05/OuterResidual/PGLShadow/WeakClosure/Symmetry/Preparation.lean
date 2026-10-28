module
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Configuration
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Conjugator
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.PGLShadow.WeakClosure.Complement

/-!
# Preparation for symmetry of the marked PGL₂ action

The adapted conjugator retains both K′ and L′, marks z as r, and transports
the given weak closure. Sylow maximality identifies the two versions of
T_E. Its abelianity excludes nonabelian two-subgroups in C_G(E), and the
independent marked generators give the nonfusion of z and v.

`OppositeInducesOuterPGL` uses the actual action of z on L′ and the
transported L′ ≃ PSL₂ equivalence. `OppositeReflection` is an output
specification for the remaining opposite geometry. Neither definition
asserts the symmetry conclusion or constructs its missing witnesses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.6, printed p.1185, the symmetry and transvection paragraphs.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
open Subgroup Theory.GroupTheory GorensteinWalter
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r v : G} {L R : Subgroup G}

theorem z_normalizes_opposite_component (h : IntersectionSetup T z L g R) :
    z ∈ normalizer (L.conjBy g : Set G) := by
  have hN : normalizer (L.conjBy g : Set G) =
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) := by
    change normalizer (L.map (MulAut.conj g).toMonoidHom : Set G) =
      normalizer ((centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom : Set G)
    rw [← map_equiv_normalizer_eq, ← map_equiv_normalizer_eq, h.normalizers_eq]
  rw [hN]
  exact h.z_normalizes_conjugate

/-- The actual conjugation action of z on the opposite component. -/
def oppositeAction (h : IntersectionSetup T z L g R) : MulAut (L.conjBy g) :=
  (L.conjBy g).normalizerMonoidHom ⟨z, z_normalizes_opposite_component h⟩

theorem oppositeAction_apply (h : IntersectionSetup T z L g R) (x : L.conjBy g) :
    (oppositeAction h x : G) = MulAut.conj z x := rfl

variable {F : Type*} [Field F]
/-- The given PSL₂ identification transported with the actual component. -/
def oppositeEquiv (e : L ≃* PSL2 F) (g : G) : L.conjBy g ≃* PSL2 F :=
  ((MulAut.conj g).subgroupMap L).symm.trans e

/-- The symmetry conclusion expressed as projective conjugation equations. -/
def OppositeInducesOuterPGL (h : IntersectionSetup T z L g R)
    (e : L ≃* PSL2 F) : Prop :=
  ∃ A : PGL2 F,
    A ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ∧
    ∀ x : L.conjBy g,
      Matrix.ProjectiveSpecialLinearGroup.toPGL (oppositeEquiv e g (oppositeAction h x)) =
        A * Matrix.ProjectiveSpecialLinearGroup.toPGL (oppositeEquiv e g x) * A⁻¹

/-- The opposite reflection still to be constructed from the symmetric outer
PGL action. This is an output specification, not a source hypothesis.
The fixed equations, distinctness of the lines, axes, and commutator centers
are derived by the final assembly from these geometric assertions. -/
structure OppositeReflection (T : Sylow 2 G) (z r : G) (L : Subgroup G)
    (g v u s : G) : Prop where
  v_not_mem : v ∉ L.conjBy g
  u_order : orderOf u = 2
  intersection_eq : markedEight z r v ⊓ L.conjBy g = zpowers u
  center_eq : embeddedCenter ((T : Subgroup G).conjBy g) = zpowers r ⊔ zpowers u
  eight_eq : markedEight r z u = markedEight z r v
  s_mem : s ∈ (T : Subgroup G).conjBy g ⊓
    normalizer (commonCentralizer (T : Subgroup G) z r : Set G)
  s_z : MulAut.conj s z = z * u

/-- The marked choice retains K′ and L′ and transports the supplied weak closure. -/
theorem exists_weakly_closed_marked_conjugator (h : IntersectionSetup T z L g R)
    (hr2 : orderOf r = 2) (hR : R = zpowers r)
    (hw : WeaklyClosedInCenter (T : Subgroup G) z) :
    ∃ a : G, IntersectionSetup T z L a R ∧
      (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g ∧
      L.conjBy a = L.conjBy g ∧
      (T : Subgroup G) ⊓ normalizer ((centralizer (L : Set G)).conjBy a : Set G) ≤
        (T : Subgroup G).conjBy a ∧ MulAut.conj a z = r ∧
      WeaklyClosedInCenter ((T : Subgroup G).conjBy a) r := by
  obtain ⟨a, ha, hK, hL, hT, hz⟩ := exists_marked_conjugator h hr2 hR
  exact ⟨a, ha, hK, hL, hT, hz, hz ▸ hw.conjBy a⟩

/-- E-centralization places the original T_E in the adapted opposite Sylow. -/
theorem commonCentralizer_le_opposite_sylow (h : IntersectionSetup T z L g R)
    (hr2 : orderOf r = 2) (hR : R = zpowers r)
    (htransport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
        (T : Subgroup G).conjBy g) :
    commonCentralizer (T : Subgroup G) z r ≤ (T : Subgroup G).conjBy g := by
  have hRne : R ≠ ⊥ := by
    rw [hR]
    intro hbot
    have hr1 : r = 1 := by simpa only [hbot, mem_bot] using mem_zpowers r
    simp [hr1] at hr2
  apply le_trans _ htransport
  apply le_inf inf_le_left
  apply le_trans _ (h.normalizer_le hRne le_rfl)
  apply le_trans _ (Subgroup.centralizer_le_normalizer _)
  exact inf_le_right.trans (centralizer_le (by rw [hR]; exact fun _ hx => mem_sup_left hx))

/-- The two choices compute the same Sylow subgroup of C_G(E). -/
theorem commonCentralizer_opposite_eq (h : IntersectionSetup T z L g R)
    (hr2 : orderOf r = 2) (hR : R = zpowers r)
    (htransport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
        (T : Subgroup G).conjBy g)
    (hn : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G))) :
    commonCentralizer ((T : Subgroup G).conjBy g) r z =
      commonCentralizer (T : Subgroup G) z r := by
  have hE : involutionPair r z = involutionPair z r := sup_comm _ _
  exact (commonCentralizer_sylow h hR hn).maximal
    ((T.isPGroup'.map (MulAut.conj g).toMonoidHom).of_injective
      (inclusion inf_le_left) (inclusion_injective _))
    (by unfold commonCentralizer; rw [hE]; exact inf_le_right)
    (le_inf (commonCentralizer_le_opposite_sylow h hr2 hR htransport)
      (by unfold commonCentralizer; rw [hE]; exact inf_le_right))

omit [Finite G] in
/-- The alternatives in the constructed geometry both make T_E abelian. -/
theorem CentralizerGeometry.commonCentralizer_abelian
    (hc : CentralizerGeometry T z L r v) :
    IsMulCommutative (commonCentralizer (T : Subgroup G) z r) := by
  rcases hc.alternatives with he | he
  · rw [he]
    obtain ⟨e⟩ := hc.eight_equiv
    exact ⟨⟨fun x y => e.injective (by simp [map_mul, mul_comm])⟩⟩
  · obtain ⟨e⟩ := he
    exact ⟨⟨fun x y => e.injective (by simp [map_mul, mul_comm])⟩⟩
/-- Abelianity of the Sylow centralizer excludes any nonabelian two-subgroup
in C_G(E), the obstruction used by the natural S₆ branch. -/
theorem pair_centralizer_two_subgroup_abelian
    (h : IntersectionSetup T z L g R) (hR : R = zpowers r)
    (hn : SylowIn ((T : Subgroup G) ⊓ normalizer (R : Set G))
      (normalizer (L : Set G) ⊓ normalizer (R : Set G)))
    (hc : CentralizerGeometry T z L r v)
    {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    (hle : Q ≤ centralizer (involutionPair z r : Set G)) : IsMulCommutative Q := by
  let _ := hc.commonCentralizer_abelian
  obtain ⟨a, _, ha⟩ := (commonCentralizer_sylow h hR hn).exists_conjugate_le hQ hle
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  apply (MulAut.conj a).injective
  change MulAut.conj a ((x : G) * y) = MulAut.conj a ((y : G) * x)
  rw [map_mul, map_mul]
  exact setLike_mul_comm
    (ha ⟨x, x.property, rfl⟩) (ha ⟨y, y.property, rfl⟩)

omit [Finite G] in
theorem CentralizerGeometry.eight_card (hc : CentralizerGeometry T z L r v) :
    Nat.card (markedEight z r v) = 8 := by
  obtain ⟨e⟩ := hc.eight_equiv
  rw [Nat.card_congr e.toEquiv]
  simp [ElementaryEight, Nat.card_eq_fintype_card]

/-- The three marked involutions are independent; in particular v is not z. -/
theorem CentralizerGeometry.v_ne_z (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hc : CentralizerGeometry T z L r v) : v ≠ z := by
  intro he
  have hc8 := hc.eight_card
  rw [he, markedEight, sup_idem, sup_comm] at hc8
  have hc4 := involutionPair_card h hr hr2
  unfold involutionPair at hc4
  omega

/-- The supplied weak closure rules out the fusion explicitly used by symmetry. -/
theorem not_isConj_z_v (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hc : CentralizerGeometry T z L r v)
    (hw : WeaklyClosedInCenter (T : Subgroup G) z) : ¬ IsConj z v := by
  intro hf
  apply hc.v_ne_z h hr hr2
  apply hw.2 v _ hf
  rw [hc.center_eq]
  exact mem_sup_right (mem_zpowers v)

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.PGLShadow.WeakClosure
