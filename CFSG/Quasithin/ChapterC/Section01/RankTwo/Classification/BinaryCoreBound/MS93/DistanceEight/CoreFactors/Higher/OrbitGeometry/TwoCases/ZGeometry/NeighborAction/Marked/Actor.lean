module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Marked.Coordinates

/-!
# The actual order-four actor and its natural fixed plane

The source edge index two restricts to the natural summand of Z_c because
the complementary summand is central in G_c and lies in Z_t. This gives
four elements in U_c intersect Z_t. The actual Q_a lies in Q_t, so centrality
of Z_t makes its marked image fix that plane pointwise. The actor's order
is independently computed from the neighboring-kernel index.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.5.4), pp.895--899.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Marked
open DistanceFour.Linear PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

include common in
/-- The source natural summand meets each edge Z-layer in a plane. -/
theorem edge_natural_card [Finite M] (earlier : Earlier R geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t) :
    Nat.card (U R c ⊓ Z R t : Subgroup (FreeAmalgam R)) = 4 := by
  let F := Z R c ⊓ centralizer (stabilizer R c : Set (FreeAmalgam R))
  have hsplit : Z R c = U R c ⊔ F :=
    (LocalCommutator.naturalStructure common).decomposition_at c hc
  have hQt : Q R t ≤ stabilizer R c := fun _ hx => hx.2 c (adjacent_symm R hct)
  have hfix := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
    (LocalCommutator.moduleFacts common) c t hc hct
  have hF : F ≤ Z R t := by
    rw [hfix]
    exact le_inf inf_le_left (inf_le_right.trans (centralizer_le hQt))
  have hUZ : U R c ≤ Z R c := U_le_Z R c
  have htZ : Z R t ≤ Z R c := Escape.EdgeTransfer.edge_Z_le c t hc hct
  have hsup : U R c ⊔ Z R t = Z R c := by
    apply le_antisymm (sup_le hUZ htZ)
    rw [hsplit]
    exact sup_le_sup_left hF _
  have hn : Z R c ≤ normalizer (Z R t : Set (FreeAmalgam R)) := by
    have htC : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) :=
      hfix ▸ inf_le_right
    exact (Escape.EdgeTransfer.edge_Z_le_Q common.large_distance c t hc hct).trans
      ((le_centralizer_iff.mp htC).trans (Subgroup.centralizer_le_normalizer _))
  let : ((Z R t).subgroupOf (Z R c)).Normal := normal_subgroupOf_of_le_normalizer hn
  have hi := relIndex_sup_right ((U R c).subgroupOf (Z R c))
    ((Z R t).subgroupOf (Z R c))
  rw [← subgroupOf_sup hUZ htZ, hsup, relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf hUZ, earlier.edge_Z_index c t hc hct] at hi
  have hcard := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (U R c ⊓ Z R t) (U R c) bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left,
    ← hi, common.natural.card_at c hc] at hcard
  omega

variable {c : Vertex R} (g : FreeAmalgam R) (hg : act R g (alpha R) = c)

/-- The literal image of the neighboring kernel in the shared marked quotient. -/
noncomputable def actor (a : Vertex R) : Subgroup S :=
  ((Q R a).subgroupOf (stabilizer R c)).map (projection common g hg)

/-- Natural coordinates of U_c intersect Z_t, with no arbitrary plane choice. -/
noncomputable def plane (t : Vertex R) : Submodule (ZMod 2) W :=
  AddSubgroup.toZModSubmodule 2
    (((Z R t).subgroupOf (U R c)).map (naturalEquiv common g hg).toMonoidHom).toAddSubgroup

theorem mem_plane (t : Vertex R) (v : W) :
    v ∈ plane common g hg t ↔ ∃ x : U R c, (x : FreeAmalgam R) ∈ Z R t ∧
      (naturalEquiv common g hg x).toAdd = v := Iff.rfl

theorem plane_card [Finite M] (earlier : Earlier R geometry)
    {t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t) :
    Nat.card (plane common g hg t) = 4 := by
  let f : (U R c ⊓ Z R t : Subgroup (FreeAmalgam R)) → plane common g hg t :=
    fun x => ⟨(naturalEquiv common g hg ⟨x, x.property.1⟩).toAdd,
      ⟨⟨x, x.property.1⟩, x.property.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      have he := (naturalEquiv common g hg).injective
        (Multiplicative.toAdd.injective (congrArg Subtype.val h))
      exact congrArg (fun z : U R c => (z : FreeAmalgam R)) he
    · intro v
      obtain ⟨x, hx, he⟩ := (mem_plane common g hg t v).mp v.property
      refine ⟨⟨x, x.property, hx⟩, ?_⟩
      exact Subtype.ext he
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  exact edge_natural_card common earlier hc hct

theorem actor_card [Finite M] (earlier : Earlier R geometry)
    {a t : Vertex R} (ha : color R a = false)
    (hca : (cosetGraph R).dist c a = 2)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a)
    (hH : Nat.card (H R a) = 4) : Nat.card (actor common g hg a) = 4 := by
  have hQa : Q R a ≤ stabilizer R c :=
    Q_le_stabilizer_of_dist_two R a c ha (by rw [SimpleGraph.dist_comm]; exact hca)
  rw [actor, ← relIndex_ker, projection_kernel, relIndex_subgroupOf hQa]
  exact neighbor_kernel_index common earlier ha hca hat hct hVa hH

theorem actor_fixes_plane [Finite M] {a t : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (k : S) (hk : k ∈ actor common g hg a) (v : W) (hv : v ∈ plane common g hg t) :
    k.val.mulVec v = v := by
  obtain ⟨q, hq, rfl⟩ := hk
  obtain ⟨x, hx, rfl⟩ := (mem_plane common g hg t v).mp hv
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hqQt := Q_le_adjacent_h R ht hat hq
  have hfixed := Escape.EdgeTransfer.edge_Z_eq_fixed common.large_distance
    (LocalCommutator.moduleFacts common) c t hc hct
  have hxC : (x : FreeAmalgam R) ∈ centralizer (Q R t : Set (FreeAmalgam R)) :=
    (hfixed ▸ hx).2
  apply (natural_action common g hg q x x ?_).symm
  have he := hxC q hqQt
  calc
    (x : FreeAmalgam R) = (x : FreeAmalgam R) * q * (q : FreeAmalgam R)⁻¹ := by simp
    _ = (q : FreeAmalgam R) * x * (q : FreeAmalgam R)⁻¹ := by rw [he]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Marked
