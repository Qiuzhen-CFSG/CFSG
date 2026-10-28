module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Edges

/-!
# The faithful matrix criterion for the selected neighbors

Use the actual natural coordinates supplied by the contrary local facts.
Their marked projection has kernel Q_c, so C_A(D) = Q_c means precisely
that no nonidentity matrix in the image of A fixes the image of D pointwise.
The statement concerns the relative centralizer inside A, not the ambient
centralizer or the setwise stabilizer of the displacement plane.

For A = Q_t and D = [Z_c,Q_s], this gives the exact finite-action test used
in the display before MS93 (4.3.2)(4). The displacement image has order four
by transport of the supplied initial facts. These lemmas translate that
test; they do not yet prove that the selected neighbors generate V_c.

Source: Meierfrankenfeld--Stellmacher (1993), printed p.884.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

abbrev Space := Multiplicative (Fin 3 → ZMod 2)

noncomputable def markedProjection {c : Vertex R} (o : OppositeSectionAt c) :
    stabilizer R c →* SL := o.naturalU.marking.toMonoidHom.comp o.projection

noncomputable def naturalEquiv {c : Vertex R} (o : OppositeSectionAt c) :
    U R c ≃* Space :=
  (subgroupOfEquivOfLe ((U_le_Z c).trans (Z_le_stabilizer R c))).symm.trans
    o.naturalU.equivOfBot

theorem markedProjection_kernel {c : Vertex R} (o : OppositeSectionAt c) :
    (markedProjection o).ker = (Q R c).subgroupOf (stabilizer R c) := by
  ext x
  change o.naturalU.marking (o.projection x) = 1 ↔ _
  rw [← o.naturalU.marking.map_one, o.naturalU.marking.injective.eq_iff,
    ← MonoidHom.mem_ker, o.kernel]

/-- The coordinates retain the actual conjugation action in the amalgam. -/
theorem naturalEquiv_conjugation {c : Vertex R} (o : OppositeSectionAt c)
    (g : stabilizer R c) (u v : U R c)
    (hv : (v : FreeAmalgam R) = g * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹) :
    (naturalEquiv o v).toAdd =
      (markedProjection o g).val.mulVec (naturalEquiv o u).toAdd := by
  exact o.naturalU.action g (mem_top g) _ _ (Subtype.ext hv)

noncomputable def naturalImage {c : Vertex R} (o : OppositeSectionAt c)
    (D : Subgroup (FreeAmalgam R)) : Subgroup Space :=
  (D.subgroupOf (U R c)).map (naturalEquiv o).toMonoidHom

noncomputable def actorImage {c : Vertex R} (o : OppositeSectionAt c)
    (A : Subgroup (FreeAmalgam R)) : Subgroup SL :=
  (A.subgroupOf (stabilizer R c)).map (markedProjection o)

/-- Pointwise fixation of actual vectors; this is not setwise stabilization. -/
def Fixes (g : SL) (D : Subgroup Space) : Prop :=
  ∀ v ∈ D, g.val.mulVec v.toAdd = v.toAdd

theorem fixes_iff_centralizes {c : Vertex R} (o : OppositeSectionAt c)
    (D : Subgroup (FreeAmalgam R)) (hD : D ≤ U R c)
    (g : stabilizer R c) :
    Fixes (markedProjection o g) (naturalImage o D) ↔
      (g : FreeAmalgam R) ∈ centralizer (D : Set (FreeAmalgam R)) := by
  constructor
  · intro h d hd
    let u : U R c := ⟨d, hD hd⟩
    have hv : (g : FreeAmalgam R) * d * (g : FreeAmalgam R)⁻¹ ∈ U R c :=
      le_normalizer_iff.mp (U_normalized c) g g.property d (hD hd)
    let v : U R c := ⟨(g : FreeAmalgam R) * d * (g : FreeAmalgam R)⁻¹, hv⟩
    have hcoord : naturalEquiv o v = naturalEquiv o u := by
      apply Multiplicative.toAdd.injective
      rw [naturalEquiv_conjugation o g u v rfl]
      exact h _ (mem_map_of_mem _ (show u ∈ D.subgroupOf (U R c) from hd))
    have heq : (g : FreeAmalgam R) * d * (g : FreeAmalgam R)⁻¹ = d :=
      congrArg Subtype.val ((naturalEquiv o).injective hcoord)
    exact (mul_inv_eq_iff_eq_mul.mp heq).symm
  · intro h v hv
    obtain ⟨u, hu, rfl⟩ := hv
    have heq : (u : FreeAmalgam R) = g * (u : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹ := by
      rw [← h u hu, mul_inv_cancel_right]
    exact (naturalEquiv_conjugation o g u u heq).symm

/-- The exact kernel criterion for a relative centralizer. -/
theorem centralizer_eq_iff {c : Vertex R} (o : OppositeSectionAt c)
    (A D : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R c) (hQ : Q R c ≤ A) (hD : D ≤ U R c) :
    A ⊓ centralizer (D : Set (FreeAmalgam R)) = Q R c ↔
      ∀ g ∈ actorImage o A, Fixes g (naturalImage o D) → g = 1 := by
  constructor
  · intro heq g hg hfix
    obtain ⟨x, hx, rfl⟩ := hg
    have hxQ : (x : FreeAmalgam R) ∈ Q R c := heq ▸
      (show (x : FreeAmalgam R) ∈ A ⊓ centralizer (D : Set (FreeAmalgam R)) from
        ⟨hx, (fixes_iff_centralizes o D hD x).mp hfix⟩)
    exact MonoidHom.mem_ker.mp ((markedProjection_kernel o).symm ▸ hxQ)
  · intro h
    apply le_antisymm
    · rintro x ⟨hx, hxc⟩
      let g : stabilizer R c := ⟨x, hA hx⟩
      have hg : markedProjection o g = 1 :=
        h _ (mem_map_of_mem _ hx) ((fixes_iff_centralizes o D hD g).mpr hxc)
      have hk := MonoidHom.mem_ker.mpr hg
      rw [markedProjection_kernel] at hk
      exact hk
    · intro x hx
      refine ⟨hQ hx, ?_⟩
      let g : stabilizer R c := ⟨x, hx.1⟩
      apply (fixes_iff_centralizes o D hD g).mp
      have hg : markedProjection o g = 1 :=
        MonoidHom.mem_ker.mp ((markedProjection_kernel o).symm ▸ hx)
      intro v hv
      rw [hg]
      exact Matrix.one_mulVec v.toAdd

variable [Finite M]

/-- The source centralizer condition is exactly a faithful pointwise action
of the edge actor on the displacement plane in the actual marking. -/
theorem edge_centralizer_eq_iff (source : LocalSource L R)
    {c t s : Vertex R} (hc : color R c = false)
    (hct : Adjacent R c t) (hcs : Adjacent R c s) (o : OppositeSectionAt c) :
    Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c ↔
      ∀ g ∈ actorImage o (Q R t),
        Fixes g (naturalImage o (edgeDisplacement c s)) → g = 1 := by
  apply centralizer_eq_iff o
  · exact fun _ hx => hx.2 c (adjacent_symm R hct)
  · apply Q_le_adjacent_h R _ hct
    have hn := adjacent_color_ne R hct
    cases ht : color R t <;> simp_all
  · exact Initial.edge_le_natural source c s hc hcs

/-- The selected source planes have their literal four elements. -/
theorem edge_image_card (source : LocalSource L R) (p : Counterexample geometry)
    (hb : 0 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    {c s : Vertex R} (hc : color R c = false) (hcs : Adjacent R c s)
    (o : OppositeSectionAt c) : Nat.card (naturalImage o (edgeDisplacement c s)) = 4 := by
  rw [naturalImage, ← Nat.card_congr
    (((edgeDisplacement c s).subgroupOf (U R c)).equivMapOfInjective
      (naturalEquiv o).toMonoidHom (naturalEquiv o).injective).toEquiv]
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (Initial.edge_le_natural source c s hc hcs)).toEquiv]
  exact FirstPairing.StepThree.edge_card p hb initial c s hc hcs

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
