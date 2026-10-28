module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.Weyl
public import Theory.SpecificGroups.SymplecticFour.WeylFrame.FixedCosets
public import Theory.GroupAction.DihedralPolygon.FixedQuadrangle

/-!
# The canonical Cartan-fixed apartment in a small symplectic completion

Inner-times-middle factorization gives native representatives for every
neighbor in the full extended geometry. The two native fixed-coset calculations
therefore identify exactly two Cartan-fixed neighbors at each endpoint, with
the original Weyl markings. Short-geodesic uniqueness preserves Cartan fixation.
Girth eight and diameter four then close the alternating Weyl arc after eight
edges. The extended-Borel centralizer calculation kills its group-action kernel,
yielding the literal relation (st)⁴ = 1 from the original order bound.

This establishes the native-compatible apartment step of the nonbinary Cartan
route in Aschbacher–Smith F.4.10 and F.4.16, printed pp.279,282 of
`refs/quasithin.pdf`. The field-four case and arbitrary extension factors are
included. Group identification follows through the paired completion.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2]
namespace SourceExtension
variable (E : SourceExtension F)

def nativeLeft : pointParabolic (F := F) →* E.left :=
  ((MulAut.conj : Sp F →* MulAut (Sp F)).comp pointParabolic.subtype).codRestrict E.left
    (fun g => (E.left_inner.ge ⟨g,g.property,rfl⟩).1)

def nativeRight : planeParabolic (F := F) →* E.right :=
  ((MulAut.conj : Sp F →* MulAut (Sp F)).comp planeParabolic.subtype).codRestrict E.right
    (fun g => (E.right_inner.ge ⟨g,g.property,rfl⟩).1)
end SourceExtension

namespace Completion
variable {E : SourceExtension F} {M : Type*} [Group M] (c : Completion E M)

def nativeMap : (i : Bool) → FlagPaths.family (F := F) i →* M
  | false => c.left.comp E.nativeLeft
  | true => c.right.comp E.nativeRight

omit [CharP F 2] in
private theorem nativeMap_mem (i : Bool) (g : FlagPaths.family (F := F) i) :
    c.nativeMap i g ∈ c.cosetFamily i := by
  cases i
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

omit [CharP F 2] in
private theorem borel_le_family (i : Bool) : borel (F := F) ≤ FlagPaths.family i := by
  cases i
  · exact inf_le_left
  · exact inf_le_right

private theorem nativeMap_borel (i : Bool) (g : borel (F := F)) :
    c.nativeMap i ⟨g.val,borel_le_family i g.property⟩ = c.borelMap g := by
  cases i
  · rfl
  · exact (DFunLike.congr_fun c.compatible (E.borelToMiddle g)).symm

private theorem nativeMap_torus (i : Bool) (p : Fˣ × Fˣ) :
    c.nativeMap i ⟨diagonalTorus p.1 p.2,borel_le_family i (diagonalTorus_mem_borel _ _)⟩ =
      c.torusMap p := c.nativeMap_borel i (torusToBorel p)

private theorem nativeMap_mem_middle (i : Bool) (g : FlagPaths.family (F := F) i) :
    c.nativeMap i g ∈ c.middle.range ↔ g.val ∈ borel := by
  constructor
  · rintro ⟨b,hb⟩
    have he : MulAut.conj g.val=b.val := by
      cases i
      · exact (congrArg Subtype.val (c.left_injective hb)).symm
      · exact (congrArg Subtype.val (c.right_injective
          ((DFunLike.congr_fun c.compatible b).symm.trans hb))).symm
    have hm : MulAut.conj g.val ∈ E.middle ⊓ inner F := ⟨he ▸ b.property,⟨_,rfl⟩⟩
    obtain ⟨u,hu,he'⟩ := E.middle_inner.le hm
    exact SourceExtension.inner_injective (F := F) he' ▸ hu
  · intro hg
    rw [show c.nativeMap i g=c.borelMap ⟨g.val,hg⟩ from c.nativeMap_borel i ⟨g.val,hg⟩]
    exact ⟨_,rfl⟩

omit [CharP F 2] in
private theorem fixes_base (g : M) (i : Bool) :
    g • base c.cosetFamily i=base c.cosetFamily i ↔ g∈c.cosetFamily i := by
  change g∈MulAction.stabilizer M (base c.cosetFamily i) ↔ _
  rw [base,Subgroup.CosetGeometry.stabilizer_base]

omit [CharP F 2] in
private theorem middle_fixes (a : E.middle) (i : Bool) :
    c.middle a • base c.cosetFamily i=base c.cosetFamily i := by
  apply (c.fixes_base _ i).mpr
  cases i
  · exact c.middle_le_left ⟨a,rfl⟩
  · exact c.middle_le_right ⟨a,rfl⟩

omit [CharP F 2] in
/-- Even in an extended completion, all neighbors have native representatives:
the common extension factor fixes the other base vertex. -/
theorem neighbor_native_rep (i : Bool) (v : Vertex c.cosetFamily)
    (hv : (graph c.cosetFamily).Adj (base c.cosetFamily i) v) :
    ∃ g : FlagPaths.family (F := F) i,
      c.nativeMap i g • base c.cosetFamily (!i)=v := by
  obtain ⟨a,ha,he⟩ := neighbor_base_rep c.cosetFamily i hv
  have he' : a • base c.cosetFamily (!i)=v := by
    change mkVertex c.cosetFamily (!i) (a*1)=v
    simpa only [mul_one] using he
  cases i
  · obtain ⟨u,rfl⟩ := ha
    obtain ⟨g,hg,b,hb,hu⟩ := E.left_factor u.val u.property
    have hu' : u=E.nativeLeft ⟨g,hg⟩*E.amalgam.left ⟨b,hb⟩ := Subtype.ext hu
    refine ⟨⟨g,hg⟩,?_⟩
    rw [hu',map_mul,mul_smul] at he'
    change c.left (E.nativeLeft ⟨g,hg⟩) • (c.middle ⟨b,hb⟩ • base c.cosetFamily (!false))=v at he'
    rw [c.middle_fixes] at he'
    exact he'
  · obtain ⟨u,rfl⟩ := ha
    obtain ⟨g,hg,b,hb,hu⟩ := E.right_factor u.val u.property
    have hu' : u=E.nativeRight ⟨g,hg⟩*E.amalgam.right ⟨b,hb⟩ := Subtype.ext hu
    have hright : c.right (E.amalgam.right ⟨b,hb⟩)=c.middle ⟨b,hb⟩ :=
      (DFunLike.congr_fun c.compatible ⟨b,hb⟩).symm
    refine ⟨⟨g,hg⟩,?_⟩
    rw [hu',map_mul,hright,mul_smul,c.middle_fixes] at he'
    exact he'

def TorusFixed (v : Vertex c.cosetFamily) : Prop := ∀p,c.torusMap p • v=v

def nativeReflection : (i : Bool) → FlagPaths.family (F := F) i
  | false => ⟨WeylFrame.pointReflection,WeylFrame.pointReflection_mem⟩
  | true => ⟨WeylFrame.planeReflection,WeylFrame.planeReflection_mem⟩

private theorem reflection_sq (i : Bool) : (nativeReflection (F := F) i)^2=1 := by
  cases i
  · exact Subtype.ext WeylFrame.pointReflection_sq
  · exact Subtype.ext WeylFrame.planeReflection_sq

/-- The full Cartan fixes precisely the two native Weyl neighbors at either
marked endpoint; the proof retains the entire extension factor. -/
theorem torus_fixed_neighbors [Finite F] (hq : 2 < Nat.card F)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (i : Bool) (v : Vertex c.cosetFamily)
    (hv : (graph c.cosetFamily).Adj (base c.cosetFamily i) v) (hf : c.TorusFixed v) :
    v=base c.cosetFamily (!i) ∨
      v=c.nativeMap i (nativeReflection i) • base c.cosetFamily (!i) := by
  obtain ⟨g,rfl⟩ := c.neighbor_native_rep i v hv
  have hh (a b : Fˣ) : g.val⁻¹*diagonalTorus a b*g.val∈borel := by
    let t : FlagPaths.family (F := F) i := ⟨diagonalTorus a b,borel_le_family i (diagonalTorus_mem_borel _ _)⟩
    have hconj : c.nativeMap i (g⁻¹*t*g) • base c.cosetFamily (!i)=base c.cosetFamily (!i) := by
      have h := hf (a,b)
      rw [←c.nativeMap_torus i (a,b)] at h
      simpa only [map_mul,map_inv,mul_smul,inv_smul_smul] using congrArg ((c.nativeMap i g)⁻¹ • ·) h
    apply (c.nativeMap_mem_middle i (g⁻¹*t*g)).mp
    rw [←ho]
    have hown := c.nativeMap_mem i (g⁻¹*t*g)
    have hother := (c.fixes_base _ (!i)).mp hconj
    cases i
    · exact ⟨hown,hother⟩
    · exact ⟨hother,hown⟩
  have hcases : g.val∈borel ∨ (nativeReflection i*g).val∈borel := by
    cases i
    · exact WeylFrame.point_fixed_coset hq g.val g.property hh
    · exact WeylFrame.plane_fixed_coset hq g.val g.property hh
  have fixes {u : FlagPaths.family (F := F) i} (hu : u.val∈borel) :
      c.nativeMap i u • base c.cosetFamily (!i)=base c.cosetFamily (!i) := by
    obtain ⟨b,hb⟩ := (c.nativeMap_mem_middle i u).mpr hu
    rw [←hb]
    exact c.middle_fixes b (!i)
  rcases hcases with h | h
  · exact Or.inl (fixes h)
  · right
    have h2 : c.nativeMap i (nativeReflection i)*c.nativeMap i (nativeReflection i)=1 := by
      rw [←map_mul,←pow_two,reflection_sq,map_one]
    have h' := congrArg (c.nativeMap i (nativeReflection i) • ·) (fixes h)
    rw [map_mul,mul_smul,←mul_smul, h2,one_smul] at h'
    exact h'

private theorem torus_fixed_base (i : Bool) : c.TorusFixed (base c.cosetFamily i) := by
  intro p
  exact c.middle_fixes (E.borelToMiddle (torusToBorel p)) i

private theorem torus_fixed_involution (u : M) (hu : u^2=1)
    (hrot : ∀p,∃q,u*c.torusMap p*u=c.torusMap q) (v : Vertex c.cosetFamily) :
    c.TorusFixed (u • v) ↔ c.TorusFixed v := by
  have huu : u*u=1 := by simpa only [pow_two] using hu
  have hf (z : Vertex c.cosetFamily) (hz : c.TorusFixed z) : c.TorusFixed (u • z) := by
    intro p
    obtain ⟨q,hq⟩ := hrot p
    calc
      c.torusMap p • (u • z) = u • ((u*c.torusMap p*u) • z) := by
        simp only [mul_smul,←mul_smul u u,huu,one_smul]
      _ = u • z := by rw [hq,hz q]
  refine ⟨fun hv => ?_,hf v⟩
  simpa only [←mul_smul,huu,one_smul] using hf (u • v) hv

private theorem torus_fixed_pointWeyl (v : Vertex c.cosetFamily) :
    c.TorusFixed (c.left E.pointWeyl • v) ↔ c.TorusFixed v :=
  c.torus_fixed_involution _ (by rw [←map_pow,E.pointWeyl_sq,map_one])
    (fun p => ⟨(p.1,p.2⁻¹),c.pointWeyl_torus _ _⟩) v

private theorem torus_fixed_planeWeyl (v : Vertex c.cosetFamily) :
    c.TorusFixed (c.right E.planeWeyl • v) ↔ c.TorusFixed v :=
  c.torus_fixed_involution _ (by rw [←map_pow,E.planeWeyl_sq,map_one])
    (fun p => ⟨(p.2,p.1),c.planeWeyl_torus _ _⟩) v

omit [CharP F 2] in
def bipartiteAction : GroupAction.DihedralPolygon.BipartiteAction M (graph c.cosetFamily) where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := c.graphAction.map_adj
  smul_color _ _ := rfl

variable [Finite F]
/-- The Cartan's two fixed neighbors force the canonical apartment to close.
No cycle marking or Weyl relation is an extra premise. -/
theorem weylProduct_four_eq_one_of_diameter {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hdiam : ∀v w,(graph c.cosetFamily).dist v w≤4) : c.weylProduct^4=1 := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1<2^n from Nat.pow_lt_pow_right (by decide) hn)
  let s := c.left E.pointWeyl
  let t := c.right E.planeWeyl
  let x := base c.cosetFamily false
  let y := base c.cosetFamily true
  have hs : s^2=1 := by dsimp [s]; rw [←map_pow,E.pointWeyl_sq,map_one]
  have ht : t^2=1 := by dsimp [t]; rw [←map_pow,E.planeWeyl_sq,map_one]
  have hsx : s • x=x := (c.fixes_base _ false).mpr ⟨_,rfl⟩
  have hty : t • y=y := (c.fixes_base _ true).mpr ⟨_,rfl⟩
  have hsy : s • y≠y := by
    intro hh
    have hm : s∈c.middle.range := ho ▸
      show s∈c.left.range⊓c.right.range from ⟨⟨_,rfl⟩,(c.fixes_base _ true).mp hh⟩
    exact WeylFrame.pointReflection_not_mem
      ((c.nativeMap_mem_middle false (nativeReflection false)).mp hm).2
  have htx : t • x≠x := by
    intro hh
    have hm : t∈c.middle.range := ho ▸
      show t∈c.left.range⊓c.right.range from ⟨(c.fixes_base _ false).mp hh,⟨_,rfl⟩⟩
    exact WeylFrame.planeReflection_not_mem
      ((c.nativeMap_mem_middle true (nativeReflection true)).mp hm).1
  have hh := GroupAction.DihedralPolygon.QuadrangleApartment.fixed_edge_sequence_closes
    c.bipartiteAction s t x y hs ht hsx hty
    ⟨Bool.false_ne_true,Subgroup.CosetGeometry.incident_base c.cosetFamily false true⟩
    hsy htx c.connected hdiam (c.cycle_length_ge_eight ho)
    c.TorusFixed (c.torus_fixed_base false) (c.torus_fixed_base true)
    c.torus_fixed_pointWeyl c.torus_fixed_planeWeyl
    (c.torus_fixed_neighbors hq ho false) (c.torus_fixed_neighbors hq ho true) (by
      intro v w p hp hl hv hw u hu z
      exact SimpleGraph.QuadrangleApartment.short_geodesic_fixed
        (c.cycle_length_ge_eight ho) c.graphAction p hp hl _ (hv z) (hw z) u hu)
  apply (c.weylProduct_four_eq_one_iff_fixes_edge hF hn ho).mpr
  exact ⟨GroupAction.DihedralPolygon.inverse_rotation_fixed ht hs hh.1,
    GroupAction.DihedralPolygon.inverse_rotation_fixed ht hs hh.2⟩

/-- The original full-extension order bound supplies the native-compatible
Weyl relation, including all extension degrees and q = 4. -/
theorem weylProduct_four_eq_one [Finite M] {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : c.weylProduct^4=1 := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1<2^n from Nat.pow_lt_pow_right (by decide) hn)
  exact c.weylProduct_four_eq_one_of_diameter hF hn ho (c.quadrangle ho hq hcard).2.1
end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
