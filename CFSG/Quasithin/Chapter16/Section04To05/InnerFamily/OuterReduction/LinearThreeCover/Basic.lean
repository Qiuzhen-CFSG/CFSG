module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.Setup
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.Consequences
public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis

/-!
# The double cover in the linear-three branch of 16.4.9

The actual PSL₃(4) quotient excludes the second commuting-Sylow alternative.
The center is the two-core by the even-type component theorem. Its image is
a central two-subgroup of C_G(L), so it lies in T_C = ⟨z⟩; nontriviality then
identifies it with that subgroup of order two.

The remaining definitions retain the actual quotient action, embedded residual,
parabolics and normalizer action. `FieldParabolicGeometry` and `GraphGeometry`
are construction targets, not assumed source results. Their existence is the
remaining field and graph argument.

The printed graph quotient N_{T_L}(V)/V cannot literally be formed: r belongs
to V but not to L. We use the actual conjugation homomorphism on V and its
image, so its quotient is by its genuine kernel C_{N_{T_L}(V)}(V).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed pp.1190–1191.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LinearThreeCover
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

omit [Finite G] in
/-- The actual quotient forces the first commuting-Sylow alternative. -/
theorem commutingSylow_eq (hd : CommutingSylowDichotomy T z L)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL) :
    commutingSylow T L = zpowers z := by
  rcases hd with he | ⟨_, hne, _⟩
  · exact he
  · exact (hne ⟨e⟩).elim

/-- The nontrivial two-core has ambient center exactly ⟨z⟩. -/
theorem center_image_eq (hEven : HasEvenTypeCentralizers G)
    (h : StandardSetup T z L) (hcore : pCore 2 L ≠ ⊥)
    (hTC : commutingSylow T L = zpowers z) :
    (center L).map L.subtype = zpowers z := by
  let Z := (center L).map L.subtype
  let C := centralizer (L : Set G)
  have hZ : center L = pCore 2 L :=
    hEven.component_center_eq_twoCore h.involution h.component
  have hZC : Z ≤ C := by
    rintro x ⟨y, hy, rfl⟩
    intro a ha
    exact congrArg Subtype.val (mem_center_iff.mp hy ⟨a, ha⟩)
  have hcent : Z.subgroupOf C ≤ center C := by
    intro x hx
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    obtain ⟨y, _, hy⟩ := hx
    change (y : G) = (x : G) at hy
    change (a : G) * (x : G) = (x : G) * (a : G)
    rw [← hy]
    exact (a.property y y.property).symm
  let : (Z.subgroupOf C).Normal := ⟨fun x hx a => by
    have he := mem_center_iff.mp (hcent hx) a
    simpa only [he, mul_assoc, mul_inv_cancel, mul_one] using hx⟩
  have hZtwo : IsPGroup 2 Z := by
    change IsPGroup 2 ((center L).map L.subtype)
    rw [hZ]
    exact (pCore_isPGroup (p := 2) (G := L)).map L.subtype
  obtain ⟨S, hS⟩ := commutingSylow_sylow h
  have hle : Z ≤ zpowers z := by
    rw [← hTC, ← hS]
    intro x hx
    exact ⟨⟨x, hZC hx⟩,
      (hZtwo.comap_subtype : IsPGroup 2 (Z.subgroupOf C)).le_sylow_of_normal (N := Z.subgroupOf C) S (show (⟨x, hZC hx⟩ : C) ∈ Z.subgroupOf C from hx),
      rfl⟩
  have hne : Z ≠ ⊥ := by
    intro he
    apply hcore
    rw [← hZ]
    exact ((center L).map_eq_bot_iff_of_injective L.subtype_injective).mp he
  have hlo : 2 ≤ Nat.card Z := by
    have hp := Nat.card_pos (α := Z)
    have hn : Nat.card Z ≠ 1 := fun hc => hne ((Z.eq_bot_iff_card).mpr hc)
    omega
  apply eq_of_le_of_card_ge hle
  simpa only [Nat.card_zpowers, h.involution] using hlo



omit [Finite G] in
/-- The embedded center equality places z in the actual component. -/
theorem z_mem_component (he : (center L).map L.subtype = zpowers z) : z ∈ L := by
  exact map_subtype_le _ (he.symm ▸ mem_zpowers z)

omit [Finite G] in
/-- The intrinsic center equality retains the subgroup inclusion into G. -/
theorem center_eq (he : (center L).map L.subtype = zpowers z) :
    center L = zpowers (⟨z, z_mem_component he⟩ : L) := by
  apply map_injective L.subtype_injective
  rw [he, MonoidHom.map_zpowers]
  rfl

omit [Finite G] in
/-- The center has order two, with its generator the specified z. -/
theorem center_card (hz : orderOf z = 2)
    (he : (center L).map L.subtype = zpowers z) : Nat.card (center L) = 2 := by
  calc
    Nat.card (center L) = Nat.card ((center L).map L.subtype) :=
      (card_map_of_injective L.subtype_injective).symm
    _ = 2 := by rw [he, Nat.card_zpowers, hz]

/-- The two-core and center have the same marked ambient image. -/
theorem twoCore_image_eq (hEven : HasEvenTypeCentralizers G)
    (h : StandardSetup T z L) (hcore : pCore 2 L ≠ ⊥)
    (hd : CommutingSylowDichotomy T z L)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL) :
    (pCore 2 L).map L.subtype = zpowers z := by
  rw [← hEven.component_center_eq_twoCore h.involution h.component]
  exact center_image_eq hEven h hcore (commutingSylow_eq hd e)

/-- A specified model action, intertwined through the actual quotient by O₂(L).
The field, graph and graph-field rows use this same convention. -/
def HasQuotientAction (L : Subgroup G) (r : G) (a : MulAut Matrix.PSL3Four.PSL) : Prop :=
  ∃ hr : r ∈ normalizer (L : Set G),
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Four.PSL,
      ∀ x : L,
        e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom ⟨r, hr⟩ x)) =
          a (e (QuotientGroup.mk' (pCore 2 L) x))

/-- The binary elementary abelian model of dimension n. -/
abbrev BinarySpace (n : ℕ) := Multiplicative (Fin n → ZMod 2)

/-- The embedded U = T ∩ O²(C_L(r)) of the graph paragraph. -/
def graphU (T : Sylow 2 G) (L : Subgroup G) (r : G) : Subgroup G :=
  (T : Subgroup G) ⊓ OuterResidual.involutionResidual L r

/-- The axis ⟨z,U⟩, retained in the ambient group. -/
def graphAxis (T : Sylow 2 G) (z : G) (L : Subgroup G) (r : G) : Subgroup G :=
  zpowers z ⊔ graphU T L r

/-- The actual space V = ⟨r,z⟩U. -/
def graphSpace (T : Sylow 2 G) (z : G) (L : Subgroup G) (r : G) : Subgroup G :=
  zpowers r ⊔ graphAxis T z L r

/-- The normalizer inside T_L, not inside G or TL. -/
def graphNormalizer (T : Sylow 2 G) (z : G) (L : Subgroup G) (r : G) : Subgroup G :=
  componentSylow T L ⊓ normalizer (graphSpace T z L r : Set G)

/-- The actual conjugation action, whose kernel determines the acting quotient. -/
def graphAction (T : Sylow 2 G) (z : G) (L : Subgroup G) (r : G) :
    graphNormalizer T z L r →* MulAut (graphSpace T z L r) :=
  (graphSpace T z L r).normalizerMonoidHom.comp (inclusion inf_le_right)

omit [Finite G] in
/-- The printed quotient by V is not literal in the outer-action case.
The acting quotient must use the kernel of `graphAction` instead. -/
theorem graphSpace_not_le_graphNormalizer (hrL : r ∉ L) :
    ¬ graphSpace T z L r ≤ graphNormalizer T z L r := by
  intro hle
  exact hrL (hle (mem_sup_left (mem_zpowers r))).1.2

/-- The geometry to be constructed in the field branch. The construction must
also identify the maximal subgroups with the compatible projective parabolics;
maximality alone is not a definition of a parabolic. -/
structure FieldParabolicGeometry (L : Subgroup G) (r : G) where
  residualParabolic : Subgroup G
  coverParabolic : Subgroup G
  residual_le : residualParabolic ≤ OuterResidual.involutionResidual L r
  cover_le : coverParabolic ≤ L
  compatible : residualParabolic ≤ coverParabolic
  residual_maximal : IsCoatom (residualParabolic.subgroupOf (OuterResidual.involutionResidual L r))
  cover_maximal : IsCoatom (coverParabolic.subgroupOf L)
  invariant : r ∈ normalizer (coverParabolic : Set G)
  core_le : (pCore 2 residualParabolic).map residualParabolic.subtype ≤
    (pCore 2 coverParabolic).map coverParabolic.subtype
  core_nontrivial : pCore 2 residualParabolic ≠ ⊥
  conjugacy : ∀ v ∈ (pCore 2 residualParabolic).map residualParabolic.subtype,
    ∃ x ∈ (pCore 2 coverParabolic).map coverParabolic.subtype, MulAut.conj x r = r * v

open scoped commutatorElement

/-- The precise output required from the graph-cover calculation. The three
models are actual subgroup isomorphisms; the action is actual conjugation.
The fixed-axis and displacement clauses must be constructed, not postulated
as earlier chapter outputs. The endgame proves [N_{T_L}(V),r] = U from these
local action data. -/
structure GraphGeometry (T : Sylow 2 G) (z : G) (L : Subgroup G) (r : G) : Prop where
  u_model : Nonempty (graphU T L r ≃* BinarySpace 2)
  space_model : Nonempty (graphSpace T z L r ≃* BinarySpace 4)
  axis_model : Nonempty (graphAxis T z L r ≃* BinarySpace 3)
  axis_fixed : graphNormalizer T z L r ≤ centralizer (graphAxis T z L r : Set G)
  displacement : ∀ n ∈ graphNormalizer T z L r, ⁅n, r⁆ ∈ graphU T L r
  action_card : Nat.card (graphAction T z L r).range = 4

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LinearThreeCover
