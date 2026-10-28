module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.RelativePencil
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.Model
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.Assembly

/-!
# Generating source normalizers and the edge-stabilizer obstruction

`Choices.Assembly` constructs two adjacent vertices whose source relative
normalizers generate with the endpoint Z-layer and whose intersection lines
are distinct. All local-model and finite-plane inputs are discharged there.

The literal edge stabilizer cannot satisfy the generation premise in
`PencilFacts.two_lines`. It equals T_t = Q_t and therefore centralizes
the edge displacement, which lies in Z_t. The intersection line also
centralizes the endpoint Z-layer. If these two actor groups generated
G_a, they would fix a nontrivial subgroup of its natural module. The
supplied disjoint decomposition excludes such a fixed subgroup.

The diagnostics below preserve the obstruction to the old transcription.
On printed p.881, MS93 defines G_{a,t}
as N_{G_a}(T_t) when the two indices have their stated values. Those
indices are proved by `Propagation.edge_indices`. The symbol in (4.3.7)
on p.887 thus denotes the relative normalizer, not G_a ∩ G_t = T_t.
The source normalizer is represented in the ambient group by
`stabilizer R a ⊓ normalizer (Q R t : Set (FreeAmalgam R))`.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of
rank two* (1993), Section 4 notation, p.881, and (4.3.7)(i), p.887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

-- The same transport calculation as the private helper in
-- SectionThree/CriticalModules/LocalStructure.lean.
private theorem map_inf_centralizer {G : Type*} [Group G]
    (A B : Subgroup G) (e : G ≃* G) :
    (A ⊓ centralizer (B : Set G)).map e.toMonoidHom =
      A.map e.toMonoidHom ⊓ centralizer (B.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, hc⟩, rfl⟩
    refine ⟨mem_map_of_mem _ hx, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hc y hy)
  · rintro _ ⟨⟨x, hx, rfl⟩, hc⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using hc (e y) (mem_map_of_mem _ hy)

omit [Finite M] in
private theorem natural_fixed_bot (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (a : Vertex R) (ha : color R a = false) :
    U R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) = ⊥ := by
  have hbase : U R (alpha R) ⊓ centralizer
      (stabilizer R (alpha R) : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    apply le_trans ?_ (disjoint_iff_inf_le.mp modules.disjoint)
    exact le_inf inf_le_left (le_inf (inf_le_left.trans (U_le_Z _))
      (inf_le_right.trans (centralizer_le (Ltilde_le_stabilizer _))))
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hbase
  rw [map_inf_centralizer, ← U_act, ← stabilizer_act, Subgroup.map_bot] at hh
  simpa only [alpha, act_mVertex, one_mul] using hh

/-- The actual edge stabilizer and the critical endpoint cannot generate
the local group. MS93's generating subgroup is the relative normalizer
defined on p.881, rather than this edge stabilizer. -/
theorem edge_stabilizer_not_generating (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β t : Vertex R) (hβ : Before p.a' p.a β 1) (hat : Adjacent R p.a t) :
    (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' ≠ stabilizer R p.a := by
  intro hgen
  have hU : edgeLine p β t ≤ U R p.a :=
    inf_le_left.trans (Initial.edge_le_natural source p.a t p.color_a hat)
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    rw [p.color_a] at hn
    cases hc : color R t <;> simp_all
  have hfixEdge : edgeLine p β t ≤ centralizer
      (↑(stabilizer R p.a ⊓ stabilizer R t) : Set (FreeAmalgam R)) := by
    rw [← Q_h_eq_edge R ht hat]
    have hZ : edgeLine p β t ≤ Z R t :=
      inf_le_left.trans (edge_le_Z p hb control edge p.a t p.color_a hat)
    rw [EdgeTransfer.edge_Z_eq_fixed hb modules p.a t p.color_a hat] at hZ
    exact hZ.trans inf_le_right
  have hfixEnd : edgeLine p β t ≤ centralizer (Z R p.a' : Set (FreeAmalgam R)) := by
    have hle : edgeLine p β t ≤ edgeDisplacement p.a β := by
      rw [edgeLine_eq_inf_displacements source p hb modules initial control edge β t hβ hat]
      exact inf_le_right
    rw [← endpoint_fixed_plane source p hb modules initial control edge β hβ] at hle
    exact hle.trans inf_le_right
  have hfixed : edgeLine p β t ≤ centralizer
      (stabilizer R p.a : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mp
    rw [← hgen]
    exact sup_le (le_centralizer_iff.mp hfixEdge) (le_centralizer_iff.mp hfixEnd)
  have hbot : edgeLine p β t = ⊥ := by
    apply le_bot_iff.mp
    rw [← natural_fixed_bot source modules p.a p.color_a]
    exact le_inf hU hfixed
  have hc := edgeLine_card source p hb modules initial control edge β t hβ hat hgen
  rw [hbot, Subgroup.card_bot] at hc
  omega

/-- The requested pair of generating edge stabilizers is incompatible
with the authorized local facts. This is a diagnostic, not (4.3.7)(i). -/
theorem not_edge_stabilizer_choices (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (β : Vertex R) (hβ : Before p.a' p.a β 1) :
    ¬ ∃ t u, Adjacent R p.a t ∧
      (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a ∧
      Adjacent R p.a u ∧
      (stabilizer R p.a ⊓ stabilizer R u) ⊔ Z R p.a' = stabilizer R p.a ∧
      edgeLine p β t ≠ edgeLine p β u := by
  rintro ⟨t, _, hat, hgen, _⟩
  exact edge_stabilizer_not_generating source p hb modules initial control edge β t hβ hat hgen

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Products.Selection
