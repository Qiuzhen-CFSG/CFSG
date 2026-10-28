module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoCentralSource
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The literal residual in the central Chapter 10 branch

The source defines R_alpha=C_{D_alpha}(W_alpha), with D_alpha the
intersection of two neighboring cores. The opposite-center decomposition
and vanishing local central omega identify this centralizer with the
previously constructed triple core intersection. Multiplication gives an
actual direct-product equivalence Z_alpha × R_alpha ≃ D_alpha, and the
exceptional condition D_alpha=Z_alpha is equivalent to R_alpha=1.

The marked earlier center action constructs every geometry premise and
computes the natural center order. This does not identify C_Q(W) with R
or supply the recognition and path parameters of 10.9--10.10.
Source: DGS, Groups and Graphs (1985), notation p.153 and 10.4, pp.155--156.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P

/-- The source residual is the centralizer inside D, not inside the whole core. -/
def bTwoResidual (F₀ : Bool → Subgroup G) (m t w z : Vertex F₀) : Subgroup G :=
  D F₀ m t ⊓ centralizer ((Z F₀ w ⊔ Z F₀ z : Subgroup G) : Set G)

/-- The center span has no fixed points for the two opposite critical centers
when the earlier local central omega is trivial. -/
theorem BTwoOppositeGeometry.center_fixed_eq_bot
    (h : LocallyRankOneTriple P B) {t v m w z : Vertex F}
    (d : BTwoOppositeGeometry F t v m w z) (hω : omegaCenterIn d.actor = ⊥) :
    Z F v ⊓ centralizer ((Z F w ⊔ Z F z : Subgroup G) : Set G) = ⊥ := by
  apply bot_unique
  intro x hx
  have hz := (mem_omegaCenterIn_iff _ _).mp ((source_Z_Q_U h v).1 hx.1)
  have hc : x ∈ centralizer (d.actor : Set G) := by
    have hh : d.actor ≤ centralizer ({x} : Set G) := by
      rw [d.actor_generators]
      apply sup_le
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr (hx.2 y hy)
      · intro y hy
        exact mem_centralizer_singleton_iff.mpr (hz.2.1 y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hh hy)
  have ha : x ∈ d.actor := d.actor_generators ▸ mem_sup_right hz.1
  exact hω ▸ (mem_omegaCenterIn_iff _ _).mpr ⟨ha,hc,hz.2.2⟩

/-- The triple core intersection is the literal C_D(W) of source p.153.
The central supplement and the opposite fixed-space calculation prove equality. -/
theorem BTwoOppositeGeometry.residual_eq_source
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {t v m w z : Vertex F}
    (d : BTwoOppositeGeometry F t v m w z) (hω : omegaCenterIn d.actor = ⊥) :
    d.residual = bTwoResidual F m t w z := by
  have hRC := d.residual_centralizes h
  apply le_antisymm
  · exact le_inf (inf_le_left.trans inf_le_left) hRC
  · intro x hx
    have hZC : Z F v ≤ centralizer (d.residual : Set G) :=
      (le_centralizer_iff.mp (graph_Q_centralizes_Z h v)).trans
        (centralizer_le ((inf_le_left.trans inf_le_left).trans d.separated))
    have hprod : x ∈ (Z F v : Set G) * (d.residual : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right _ _
        (hZC.trans (Subgroup.centralizer_le_normalizer _)),←d.decomposition h hS hb]
      exact hx.1
    obtain ⟨a,ha,r,hr,rfl⟩ := hprod
    have haC : a ∈ centralizer ((Z F w ⊔ Z F z : Subgroup G) : Set G) := by
      simpa only [mul_inv_cancel_right] using
        (centralizer ((Z F w ⊔ Z F z : Subgroup G) : Set G)).mul_mem hx.2
          ((centralizer _).inv_mem (hRC hr))
    have ha1 : a = 1 := mem_bot.mp (d.center_fixed_eq_bot h hω ▸ ⟨ha,haC⟩)
    change a * r ∈ d.residual
    rw [ha1,one_mul]
    exact hr

/-- The actual multiplication map identifies D with its center and residual factors. -/
theorem BTwoOppositeGeometry.direct_product
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {t v m w z : Vertex F}
    (d : BTwoOppositeGeometry F t v m w z) (hω : omegaCenterIn d.actor = ⊥) :
    ∃ e : Z F v × bTwoResidual F m t w z ≃* D F m t,
      ∀ a r, (e (a,r) : G) = (a : G)*(r : G) := by
  have hres := d.residual_eq_source h hS hb hω
  have hdec : Z F v ⊔ bTwoResidual F m t w z = D F m t := by
    rw [←hres,←d.decomposition h hS hb]
  have hd : Disjoint (Z F v) (bTwoResidual F m t w z) := by
    apply disjoint_iff.mpr
    exact bot_unique ((inf_le_inf_left _ inf_le_right).trans
      (d.center_fixed_eq_bot h hω).le)
  have hc : Z F v ≤ centralizer (bTwoResidual F m t w z : Set G) :=
    (le_centralizer_iff.mp (graph_Q_centralizes_Z h v)).trans
      (centralizer_le (inf_le_left.trans d.separated))
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hc
  exact ⟨e.trans (MulEquiv.subgroupCongr hdec),he⟩

variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The earlier center action gives the actual residual, its internal direct
product with Z_alpha, and the exact test separating 10.9 from 10.10. -/
theorem BTwoCenterActionData.central_residual_structure
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m) :
    ∃ g : c.actor, (g : G) • m = t ∧
      let R := bTwoResidual F m t w ((g : G) • w)
      R = centralResidual F m t w ((g : G) • w) ∧
      D F m t = Z F v ⊔ R ∧
      Disjoint (Z F v) R ∧
      IsElementaryAbelian 2 R ∧
      (∃ e : Z F v × R ≃* D F m t, ∀ a r, (e (a,r) : G) = (a : G)*(r : G)) ∧
      (D F m t = Z F v ↔ R = ⊥) := by
  have hS := source_kernel_sylow h hB hSyl
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,hker⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hωd : omegaCenterIn d.actor = ⊥ := hd.symm ▸ hω
  have hr := d.residual_eq_source h hS hb hωd
  have he := d.direct_product h hS hb hωd
  have hdis : Disjoint d.residual (Z F v) := disjoint_iff.mpr
    (bot_unique (hker.trans hω.le))
  have hT : (c.sylow : Subgroup (stabilizer F v)).map (stabilizer F v).subtype ≤ d.actor :=
    hd.symm ▸ c.sylow_le_actor
  have hD := d.elementary h hS hb c.sylow hT hdis
  let R := bTwoResidual F m t w ((g : G) • w)
  have hdec : D F m t = Z F v ⊔ R := (d.decomposition h hS hb).trans (congrArg (Z F v ⊔ ·) hr)
  have hdisR : Disjoint (Z F v) R := by
    change Disjoint (Z F v) (bTwoResidual F m t w ((g : G) • w))
    rw [←hr]
    exact hdis.symm
  refine ⟨g,hg,hr.symm,hdec,hdisR,?_,he,?_⟩
  · let := hD
    exact IsElementaryAbelian.of_injective (inclusion (show R ≤ D F m t from inf_le_left))
      (inclusion_injective _)
  · constructor
    · intro hDZ
      apply bot_unique
      have hRZ : R ≤ Z F v := hDZ ▸ (show R ≤ D F m t from inf_le_left)
      exact (le_inf hRZ le_rfl).trans hdisR.le_bot
    · intro hR
      change R = ⊥ at hR
      rw [hdec,hR,sup_bot_eq]

local instance {K : Type*} [Field K] [CharP K 2] : Algebra (ZMod 2) K := ZMod.algebra K 2

/-- The actual center has the natural order after the earlier central kernel vanishes. -/
theorem BTwoCenterActionData.central_center_card
    {v m w : Vertex F} (c : BTwoCenterActionData F v m w k W)
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hω : omegaCenterIn c.actor = ⊥) :
    Nat.card (Z F v) = Nat.card k ^ 2 := by
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hh := c.coordinates.card_section
  rw [hω,Subgroup.card_bot,mul_one,
    Representation.RankOne.QuadraticRecognition.card_of_natural_coordinates E] at hh
  exact hh


end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
