module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.WeylAction
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeExtension.NativeOrder
public import Theory.SpecificGroups.ReeF4.SmallCompletion.FixedCosets
public import Theory.GroupAction.DihedralPolygon.FixedOctagon

/-!
# The native Cartan-fixed apartment in an order-bounded Ree completion

Each endpoint of the native-amalgam graph has precisely the two marked
Cartan-fixed neighbors. Unique geodesics shorter than eight preserve Cartan
fixation, so girth sixteen and diameter eight close the marked sixteen-arc.
Its eighth rotation power belongs to the actual native Borel image. The
previous Cartan-defect calculation then makes this power trivial.

For a full extension, the order bound supplies this metric on the restricted
native subcompletion. Thus no extended-middle element is mistaken for a
native Borel element. Every positive parameter, including q=8, is covered.

Source: Aschbacher–Smith F.4.10,16,24, printed pp.279,282,287–288.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory ReeF4.Parabolics ReeF4.LargeLocalSeeds
open ReeF4.SmallCompletion Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.Completion
variable {m : ℕ} {M : Type*} [Group M] (c : GeneralReeFour.Completion m M)

private def side (i : Bool) : Side := if i then .suzuki else .linear
private def localMap : (i : Bool) → parabolic m (side i) →* M
  | false => c.left
  | true => c.right

private theorem localMap_borel (i : Bool) (b : borel m) :
    localMap c i ⟨b.val,borel_le_parabolic m (side i) b.property⟩=c.middle b := by
  cases i
  · rfl
  · exact (DFunLike.congr_fun c.compatible b).symm

private theorem localMap_mem (i : Bool) (g : parabolic m (side i)) :
    localMap c i g ∈ c.cosetFamily i := by cases i <;> exact ⟨_,rfl⟩

private theorem localMap_injective (i : Bool) : Function.Injective (localMap c i) := by
  cases i
  · exact c.left_injective
  · exact c.right_injective

private theorem localMap_mem_middle (i : Bool) (g : parabolic m (side i)) :
    localMap c i g ∈ c.middle.range ↔ g.val ∈ borel m := by
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

private theorem middle_fixes (a : borel m) (i : Bool) :
    c.middle a • base c.cosetFamily i=base c.cosetFamily i := by
  apply (fixes_base c _ i).mpr
  cases i
  · exact c.middle_le_left ⟨a,rfl⟩
  · exact c.middle_le_right ⟨a,rfl⟩

/-- The full native Cartan map in the restricted completion. -/
private def cartanMap : fixedTorus m →* M := c.middle.comp (inclusion (fixedTorus_le_borel m))

/-- Cartan fixation in the actual native-amalgam coset graph. -/
private def CartanFixed (v : c.Vertex) : Prop := ∀t,c.cartanMap t • v=v

/-- At each native endpoint precisely the two marked Weyl neighbors are
Cartan fixed. In particular the common image here is the native Borel. -/
private theorem cartan_fixed_neighbors (hm : 0 < m)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (i : Bool) (v : c.Vertex)
    (hv : c.graph.Adj (base c.cosetFamily i) v) (hf : c.CartanFixed v) :
    v=base c.cosetFamily (!i) ∨
      v=localMap c i (reflection m (side i)) • base c.cosetFamily (!i) := by
  obtain ⟨a,ha,he⟩ := neighbor_base_rep c.cosetFamily i hv
  have hex : ∃ g : parabolic m (side i),localMap c i g=a := by
    cases i <;> exact ha
  obtain ⟨g,rfl⟩ := hex
  have hev : localMap c i g • base c.cosetFamily (!i)=v := by
    change mkVertex c.cosetFamily (!i) (localMap c i g*1)=v
    simpa only [mul_one] using he
  clear he
  subst v
  have hconj (t : ReeF4.Model m) (ht : t∈fixedTorus m) : g.val⁻¹*t*g.val∈borel m := by
    let u : parabolic m (side i) := ⟨t,borel_le_parabolic m (side i) (fixedTorus_le_borel m ht)⟩
    have hmap : localMap c i u=c.cartanMap ⟨t,ht⟩ :=
      localMap_borel c i ⟨t,fixedTorus_le_borel m ht⟩
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
  have fixes (u : parabolic m (side i)) (hu : u.val∈borel m) :
      localMap c i u • base c.cosetFamily (!i)=base c.cosetFamily (!i) := by
    obtain ⟨b,hb⟩ := (localMap_mem_middle c i u).mpr hu
    rw [←hb]
    exact middle_fixes c b (!i)
  rcases parabolic_fixed_coset m hm (side i) g.val g.property hconj with h | h
  · exact Or.inl (fixes g h)
  · right
    have h2 : localMap c i (reflection m (side i))*localMap c i (reflection m (side i))=1 := by
      rw [←map_mul,←pow_two,reflection_sq,map_one]
    have hh := congrArg (localMap c i (reflection m (side i)) • ·)
      (fixes (reflection m (side i)*g) h)
    rw [map_mul,mul_smul,←mul_smul,h2,one_smul] at hh
    exact hh

private theorem cartan_fixed_base (i : Bool) : c.CartanFixed (base c.cosetFamily i) := by
  intro t
  exact middle_fixes c ⟨t.val,fixedTorus_le_borel m t.property⟩ i

private theorem cartan_fixed_reflection (i : Bool) (v : c.Vertex) :
    c.CartanFixed (localMap c i (reflection m (side i)) • v) ↔ c.CartanFixed v := by
  let u := localMap c i (reflection m (side i))
  have huu : u*u=1 := by
    dsimp [u]
    rw [←map_mul,←pow_two,reflection_sq,map_one]
  have hconj (t : fixedTorus m) : u*c.cartanMap t*u⁻¹=c.cartanMap (torusReflection m (side i) t) := by
    rw [show c.cartanMap t = localMap c i
      ⟨t.val,borel_le_parabolic m (side i) (fixedTorus_le_borel m t.property)⟩ from
      (localMap_borel c i ⟨t.val,fixedTorus_le_borel m t.property⟩).symm]
    rw [show c.cartanMap (torusReflection m (side i) t) = localMap c i
      ⟨(torusReflection m (side i) t).val,borel_le_parabolic m (side i)
        (fixedTorus_le_borel m (torusReflection m (side i) t).property)⟩ from
      (localMap_borel c i ⟨_,fixedTorus_le_borel m (torusReflection m (side i) t).property⟩).symm]
    change localMap c i _ * localMap c i _ * (localMap c i _)⁻¹ = _
    rw [←map_inv,←map_mul,←map_mul]
    rfl
  have hui : u⁻¹=u := inv_eq_of_mul_eq_one_right huu
  have forward (z : c.Vertex) (hz : c.CartanFixed z) : c.CartanFixed (u • z) := by
    intro t
    calc
      c.cartanMap t • (u • z) = u • ((u*c.cartanMap t*u⁻¹) • z) := by
        rw [hui]
        simp only [mul_smul,←mul_smul u u,huu,one_smul]
      _ = u • z := by rw [hconj,hz]
  refine ⟨fun hv => ?_,forward v⟩
  simpa only [←mul_smul,huu,one_smul] using forward (u • v) hv

private def bipartiteAction : GroupAction.DihedralPolygon.BipartiteAction M c.graph where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := c.graphAction.map_adj
  smul_color _ _ := rfl

/-- Diameter eight closes the literal marked apartment in the native graph. -/
theorem marked_eight_mem_middle_of_diameter (hm : 0 < m)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hdiam : ∀v w,c.graph.dist v w≤8) :
    (c.left (reflection m .linear)*c.right (reflection m .suzuki))^8∈c.middle.range := by
  let s := c.left (reflection m .linear)
  let t := c.right (reflection m .suzuki)
  let x := base c.cosetFamily false
  let y := base c.cosetFamily true
  have hs : s^2=1 := by dsimp [s]; rw [←map_pow,reflection_sq,map_one]
  have ht : t^2=1 := by dsimp [t]; rw [←map_pow,reflection_sq,map_one]
  have hsx : s • x=x := (fixes_base c _ false).mpr ⟨_,rfl⟩
  have hty : t • y=y := (fixes_base c _ true).mpr ⟨_,rfl⟩
  have hsy : s • y≠y := by
    intro hh
    have hm : s∈c.middle.range := ho ▸
      show s∈c.left.range⊓c.right.range from ⟨⟨_,rfl⟩,(fixes_base c _ true).mp hh⟩
    exact reflection_not_mem_borel m .linear ((localMap_mem_middle c false (reflection m .linear)).mp hm)
  have htx : t • x≠x := by
    intro hh
    have hm : t∈c.middle.range := ho ▸
      show t∈c.left.range⊓c.right.range from ⟨(fixes_base c _ false).mp hh,⟨_,rfl⟩⟩
    exact reflection_not_mem_borel m .suzuki ((localMap_mem_middle c true (reflection m .suzuki)).mp hm)
  have hh := GroupAction.DihedralPolygon.OctagonApartment.fixed_edge_sequence_closes
    (bipartiteAction c) s t x y hs ht hsx hty
    ⟨Bool.false_ne_true,Subgroup.CosetGeometry.incident_base c.cosetFamily false true⟩
    hsy htx c.connected hdiam (c.cycle_length_ge_sixteen hm ho)
    c.CartanFixed (cartan_fixed_base c false) (cartan_fixed_base c true)
    (cartan_fixed_reflection c false) (cartan_fixed_reflection c true)
    (c.cartan_fixed_neighbors hm ho false) (c.cartan_fixed_neighbors hm ho true) (by
      intro v w p hp hl hv hw u hu z
      exact SimpleGraph.OctagonApartment.short_geodesic_fixed
        (c.cycle_length_ge_sixteen hm ho) c.graphAction p hp hl _ (hv z) (hw z) u hu)
  rw [←ho]
  exact ⟨(fixes_base c _ false).mp (GroupAction.DihedralPolygon.inverse_rotation_fixed ht hs hh.1),
    (fixes_base c _ true).mp (GroupAction.DihedralPolygon.inverse_rotation_fixed ht hs hh.2)⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour.Completion

namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
variable {m : ℕ} (E : SourceExtension m) {M : Type*} [Group M] [Finite M] (c : Completion E M)

/-- The full extension order bound forces the actual marked eighth-power relation.
The closure takes place in the restricted native completion, so its common
image is literally the native Borel rather than the extended middle. -/
theorem weylProduct_eight_eq_one (hm : 0 < m)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (horder : Nat.card M≤Nat.card E.carrier) : weylProduct E c^8=1 := by
  let d := nativeCompletion E c hm
  have hd := nativeCompletion_overlap E c hm ho
  have hg := d.octagon_metric_of_order_bound hm hd Nat.lt_two_pow_self
    (nativeCore_field_bound E c hm horder)
  obtain ⟨b,hb⟩ := d.marked_eight_mem_middle_of_diameter hm hd hg.2.1
  apply (weylProduct_eight_eq_one_iff_mem_borel E c hm).mpr
  exact ⟨b,congrArg Subtype.val hb⟩
end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeExtension
