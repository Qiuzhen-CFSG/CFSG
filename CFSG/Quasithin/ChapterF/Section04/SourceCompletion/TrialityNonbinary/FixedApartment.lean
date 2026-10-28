module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.NativeOrder
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.FixedCosets
public import Theory.GroupAction.DihedralPolygon.FixedHexagon

/-!
# Closure of the marked native triality apartment

The native Cartan fixes exactly two neighbors of either base vertex. Unique
short geodesics retain Cartan fixation. Girth twelve and native diameter six
therefore close the marked twelve-arc. Its sixth rotation power lies in the
native Borel image. The full extension order bound supplies this diameter
on the actual native subgroup, even at q=4; no outer overlap element is
mistaken for an element of the native Borel. Eliminating the remaining
native Cartan defect is a further step.

Source: Aschbacher--Smith F.4.10,16,24, pp.279,282,287--288.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup Theory.GroupTheory
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open _root_.Triality.Standard.ConcreteBruhat
open Subgroup.CosetGeometry.RankTwo

/-- The actual native reflection, with its parabolic type. -/
def reflection (m : ℕ) (hm : 0 < m) (s : Node) : parabolic (binaryParameters m hm) s :=
  ⟨simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s,simpleRepresentative_mem_parabolic _ rfl s⟩

theorem reflection_sq (m : ℕ) (hm : 0 < m) (s : Node) : reflection m hm s ^ 2 = 1 :=
  Subtype.ext (simpleRepresentative_sq _ rfl s)

theorem reflection_not_mem_borel (m : ℕ) (hm : 0 < m) (s : Node) :
    (reflection m hm s).val ∉ borel (binaryParameters m hm) := by
  intro h
  have hw := (RelativeNormalizer.representative_mem_borel_iff m hm (relativeReflection s)).mp
    (show weylRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) (relativeReflection s) ∈
      borel (binaryParameters m hm) by rwa [weylRepresentative_simple _ (binaryParameters_prime m hm)])
  exact (relativeReflection_involution s).1 hw

/-- Restriction of the literal native reflection action to the entire Cartan. -/
def torusReflection (m : ℕ) (hm : 0 < m) (s : Node) : MulAut (torus (binaryParameters m hm)) :=
  (torus (binaryParameters m hm)).normalizerMonoidHom
    ⟨(reflection m hm s).val, by
      change simpleRepresentative (binaryParameters m hm) (binaryParameters_prime m hm) s ∈ _
      rw [←weylRepresentative_simple _ (binaryParameters_prime m hm)]
      exact RelativeNormalizer.weylRepresentative_normalizes_torus _ rfl _⟩

namespace NativeCompletion
variable {m : ℕ} {hm : 0 < m} {M : Type*} [Group M] (c : NativeCompletion m hm M)

private def side (i : Bool) : Node := if i then .central else .arms
private def localMap : (i : Bool) → parabolic (binaryParameters m hm) (side i) →* M
  | false => c.left
  | true => c.right

private theorem localMap_borel (i : Bool) (b : borel (binaryParameters m hm)) :
    localMap c i ⟨b.val,borel_le_parabolic (binaryParameters m hm) (side i) b.property⟩=c.middle b := by
  cases i
  · rfl
  · exact (DFunLike.congr_fun c.compatible b).symm

private theorem localMap_mem (i : Bool) (g : parabolic (binaryParameters m hm) (side i)) :
    localMap c i g ∈ c.cosetFamily i := by cases i <;> exact ⟨_,rfl⟩

private theorem localMap_injective (i : Bool) : Function.Injective (localMap c i) := by
  cases i
  · exact c.left_injective
  · exact c.right_injective

private theorem localMap_mem_middle (i : Bool) (g : parabolic (binaryParameters m hm) (side i)) :
    localMap c i g ∈ c.middle.range ↔ g.val ∈ borel (binaryParameters m hm) := by
  constructor
  · rintro ⟨b,hb⟩
    have he : b.val=g.val := congrArg Subtype.val
      (localMap_injective c i ((localMap_borel c i b).trans hb))
    exact he ▸ b.property
  · intro hg
    exact ⟨⟨g.val,hg⟩,(localMap_borel c i ⟨g.val,hg⟩).symm⟩

private theorem fixes_base (g : M) (i : Bool) :
    g • base c.cosetFamily i=base c.cosetFamily i ↔ g∈c.cosetFamily i := by
  change g∈MulAction.stabilizer M (base c.cosetFamily i) ↔ _
  rw [base,Subgroup.CosetGeometry.stabilizer_base]

private theorem middle_fixes (a : borel (binaryParameters m hm)) (i : Bool) :
    c.middle a • base c.cosetFamily i=base c.cosetFamily i := by
  apply (fixes_base c _ i).mpr
  cases i
  · exact c.middle_le_left ⟨a,rfl⟩
  · exact c.middle_le_right ⟨a,rfl⟩

/-- The full native Cartan map in the restricted completion. -/
private def cartanMap : torus (binaryParameters m hm) →* M := c.middle.comp (inclusion (torus_le_borel (binaryParameters m hm)))

/-- Cartan fixation in the actual native-amalgam coset graph. -/
private def CartanFixed (v : Vertex c.cosetFamily) : Prop := ∀t,c.cartanMap t • v=v

/-- At each native endpoint precisely the two marked Weyl neighbors are
Cartan fixed. In particular the common image here is the native Borel. -/
private theorem cartan_fixed_neighbors (hm2 : 1 < m)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (i : Bool) (v : Vertex c.cosetFamily)
    (hv : (graph c.cosetFamily).Adj (base c.cosetFamily i) v) (hf : c.CartanFixed v) :
    v=base c.cosetFamily (!i) ∨
      v=localMap c i (reflection m hm (side i)) • base c.cosetFamily (!i) := by
  obtain ⟨a,ha,he⟩ := neighbor_base_rep c.cosetFamily i hv
  have hex : ∃ g : parabolic (binaryParameters m hm) (side i),localMap c i g=a := by
    cases i <;> exact ha
  obtain ⟨g,rfl⟩ := hex
  have hev : localMap c i g • base c.cosetFamily (!i)=v := by
    change mkVertex c.cosetFamily (!i) (localMap c i g*1)=v
    simpa only [mul_one] using he
  clear he
  subst v
  have hconj (t : BinaryCarrier m hm) (ht : t∈torus (binaryParameters m hm)) : g.val⁻¹*t*g.val∈borel (binaryParameters m hm) := by
    let u : parabolic (binaryParameters m hm) (side i) := ⟨t,borel_le_parabolic (binaryParameters m hm) (side i) (torus_le_borel (binaryParameters m hm) ht)⟩
    have hmap : localMap c i u=c.cartanMap ⟨t,ht⟩ :=
      localMap_borel c i ⟨t,torus_le_borel (binaryParameters m hm) ht⟩
    have hh := hf ⟨t,ht⟩
    rw [←hmap] at hh
    have hfix : localMap c i (g⁻¹*u*g) • base c.cosetFamily (!i)=base c.cosetFamily (!i) := by
      simpa only [map_mul,map_inv,mul_smul,inv_smul_smul] using
        congrArg ((localMap c i g)⁻¹ • ·) hh
    apply (localMap_mem_middle c i (g⁻¹*u*g)).mp
    rw [←ho]
    have hown := localMap_mem c i (g⁻¹*u*g)
    have hother := (fixes_base c _ (!i)).mp hfix
    cases i
    · exact ⟨hown,hother⟩
    · exact ⟨hother,hown⟩
  have fixes (u : parabolic (binaryParameters m hm) (side i)) (hu : u.val∈borel (binaryParameters m hm)) :
      localMap c i u • base c.cosetFamily (!i)=base c.cosetFamily (!i) := by
    obtain ⟨b,hb⟩ := (localMap_mem_middle c i u).mpr hu
    rw [←hb]
    exact middle_fixes c b (!i)
  rcases parabolic_fixed_coset m hm hm2 (side i) g.val g.property hconj with h | h
  · exact Or.inl (fixes g h)
  · right
    have h2 : localMap c i (reflection m hm (side i))*localMap c i (reflection m hm (side i))=1 := by
      rw [←map_mul,←pow_two,reflection_sq,map_one]
    have hh := congrArg (localMap c i (reflection m hm (side i)) • ·)
      (fixes (reflection m hm (side i)*g) h)
    rw [map_mul,mul_smul,←mul_smul,h2,one_smul] at hh
    exact hh

private theorem cartan_fixed_base (i : Bool) : c.CartanFixed (base c.cosetFamily i) := by
  intro t
  exact middle_fixes c ⟨t.val,torus_le_borel (binaryParameters m hm) t.property⟩ i

private theorem cartan_fixed_reflection (i : Bool) (v : Vertex c.cosetFamily) :
    c.CartanFixed (localMap c i (reflection m hm (side i)) • v) ↔ c.CartanFixed v := by
  let u := localMap c i (reflection m hm (side i))
  have huu : u*u=1 := by
    dsimp [u]
    rw [←map_mul,←pow_two,reflection_sq,map_one]
  have hconj (t : torus (binaryParameters m hm)) : u*c.cartanMap t*u⁻¹=c.cartanMap (torusReflection m hm (side i) t) := by
    rw [show c.cartanMap t = localMap c i
      ⟨t.val,borel_le_parabolic (binaryParameters m hm) (side i) (torus_le_borel (binaryParameters m hm) t.property)⟩ from
      (localMap_borel c i ⟨t.val,torus_le_borel (binaryParameters m hm) t.property⟩).symm]
    rw [show c.cartanMap (torusReflection m hm (side i) t) = localMap c i
      ⟨(torusReflection m hm (side i) t).val,borel_le_parabolic (binaryParameters m hm) (side i)
        (torus_le_borel (binaryParameters m hm) (torusReflection m hm (side i) t).property)⟩ from
      (localMap_borel c i ⟨_,torus_le_borel (binaryParameters m hm) (torusReflection m hm (side i) t).property⟩).symm]
    change localMap c i _ * localMap c i _ * (localMap c i _)⁻¹ = _
    rw [←map_inv,←map_mul,←map_mul]
    rfl
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_right huu
  have forward (z : Vertex c.cosetFamily) (hz : c.CartanFixed z) : c.CartanFixed (u • z) := by
    intro t
    calc
      c.cartanMap t • (u • z) = u • ((u*c.cartanMap t*u⁻¹) • z) := by
        rw [hui]
        simp only [mul_smul,←mul_smul u u,huu,one_smul]
      _ = u • z := by rw [hconj,hz]
  refine ⟨fun hv => ?_,forward v⟩
  simpa only [←mul_smul,huu,one_smul] using forward (u • v) hv

private def bipartiteAction : GroupAction.DihedralPolygon.BipartiteAction M (graph c.cosetFamily) where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := c.graphAction.map_adj
  smul_color _ _ := rfl

/-- Diameter six closes the literal marked apartment in the native graph. -/
theorem marked_six_mem_middle_of_diameter (hm2 : 1 < m)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hdiam : ∀v w,(graph c.cosetFamily).dist v w≤6) :
    (c.left (reflection m hm .arms)*c.right (reflection m hm .central))^6∈c.middle.range := by
  let s := c.left (reflection m hm .arms)
  let t := c.right (reflection m hm .central)
  let x := base c.cosetFamily false
  let y := base c.cosetFamily true
  have hs : s^2=1 := by dsimp [s]; rw [←map_pow,reflection_sq,map_one]
  have ht : t^2=1 := by dsimp [t]; rw [←map_pow,reflection_sq,map_one]
  have hsx : s • x=x := (fixes_base c _ false).mpr ⟨_,rfl⟩
  have hty : t • y=y := (fixes_base c _ true).mpr ⟨_,rfl⟩
  have hsy : s • y≠y := by
    intro hh
    have hmem : s∈c.middle.range := ho ▸
      show s∈c.left.range⊓c.right.range from ⟨⟨_,rfl⟩,(fixes_base c _ true).mp hh⟩
    exact reflection_not_mem_borel m hm .arms ((localMap_mem_middle c false (reflection m hm .arms)).mp hmem)
  have htx : t • x≠x := by
    intro hh
    have hmem : t∈c.middle.range := ho ▸
      show t∈c.left.range⊓c.right.range from ⟨(fixes_base c _ false).mp hh,⟨_,rfl⟩⟩
    exact reflection_not_mem_borel m hm .central ((localMap_mem_middle c true (reflection m hm .central)).mp hmem)
  have hh := GroupAction.DihedralPolygon.fixed_edge_sequence_closes
    (bipartiteAction c) s t x y hs ht hsx hty
    ⟨Bool.false_ne_true,Subgroup.CosetGeometry.incident_base c.cosetFamily false true⟩
    hsy htx c.connected hdiam (c.cycle_length_ge_twelve ho)
    c.CartanFixed (cartan_fixed_base c false) (cartan_fixed_base c true)
    (cartan_fixed_reflection c false) (cartan_fixed_reflection c true)
    (c.cartan_fixed_neighbors hm2 ho false) (c.cartan_fixed_neighbors hm2 ho true) (by
      intro v w p hp hl hv hw u hu z
      exact SimpleGraph.short_geodesic_fixed
        (c.cycle_length_ge_twelve ho) c.graphAction p hp hl _ (hv z) (hw z) u hu)
  rw [←ho]
  exact ⟨(fixes_base c _ false).mp (GroupAction.DihedralPolygon.inverse_rotation_fixed ht hs hh.1),
    (fixes_base c _ true).mp (GroupAction.DihedralPolygon.inverse_rotation_fixed ht hs hh.2)⟩
end NativeCompletion

variable {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm)
variable {M : Type*} [Group M] [Finite M] (c : Completion E M)

/-- Under the full extension bound the relation defect belongs to the literal
native Borel image, even if the full extension middle has outer elements. -/
theorem marked_six_mem_native_borel (hm2 : 1 < m)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (horder : Nat.card M ≤ Nat.card E.carrier) :
    ∃ b : borel (binaryParameters m hm),
      c.left (E.nativeLeft ⟨b.val,borel_le_parabolic _ .arms b.property⟩) =
        (c.left (E.nativeLeft (reflection m hm .arms)) *
          c.right (E.nativeRight (reflection m hm .central)))^6 := by
  let d := nativeCompletion E c
  obtain ⟨b,hb⟩ := d.marked_six_mem_middle_of_diameter hm2
    (nativeCompletion_overlap E c ho) (nativeCore_diameter_le E c hm2 ho horder)
  exact ⟨b,congrArg Subtype.val hb⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
