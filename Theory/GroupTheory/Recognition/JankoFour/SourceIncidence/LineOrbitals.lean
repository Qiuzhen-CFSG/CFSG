module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.LineOrbit
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.PointChart
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Orbitals

/-!
# The five ambient line orbits under the original Todd marking

The native partition and valencies transfer through the literal point chart.
A native stabilizer transporter lifts along the original surjective Todd
projection, and chart equivariance gives its action on the original ambient
cosets. Conjugating by the same point representative transports this action
to every point. Thus these are the simultaneous point–line stabilizer orbits
required by the unchanged cycle-base input. Distinct valencies make each
orbital self-paired and supply the actual line-pair interchange used in (5.6).

Source: Aschbacher–Segev (1991), (5.4)(1),(3)–(5), pp.600–601.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

/-- The five source labels partition all lines through the same ambient point. -/
theorem orbital_partition (x : Point a.P) (l k : Line a.L)
    (hl : OnLine a.L x l) (hk : OnLine a.L x k) :
    ∃! i : Fin 5, LineType a.residueChart i x l k := by
  simpa only [lineType_at a.residueChart _ x ⟨l,hl⟩ ⟨k,hk⟩] using
    NativeLineOrbit.partition (a.residueChart.linesAt x ⟨l,hl⟩)
      (a.residueChart.linesAt x ⟨k,hk⟩)

private theorem orbital_transitive_base
    (l k m : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l}) (i : Fin 5)
    (hk : LineType a.residueChart i (Cosets.vertex a.P.M 1) l.val k.val)
    (hm : LineType a.residueChart i (Cosets.vertex a.P.M 1) l.val m.val) :
    ∃ g : a.P.M, (g : G) • l.val = l.val ∧ (g : G) • k.val = m.val := by
  obtain ⟨g,hgl,hgk⟩ := NativeLineOrbit.transitive
    (a.residueChart.lines l) (a.residueChart.lines k) (a.residueChart.lines m) i
    ((lineType_base a.residueChart i l k).mp hk)
    ((lineType_base a.residueChart i l m).mp hm)
  obtain ⟨b,hb⟩ := a.projection_surjective g
  have base : (b : G) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr b.property
  have lift (u v : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
      (huv : g • a.residueChart.lines u = a.residueChart.lines v) : (b : G) • u.val = v.val := by
    let w : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l} :=
      ⟨(b : G) • u.val,by simpa only [OnLine,base] using incident_smul (b : G) u.property⟩
    have he : a.residueChart.lines w = a.residueChart.lines v := by
      apply Native.line_parts_injective
      rw [a.residueChart.lines_equivariant b u w rfl,hb]
      exact congrArg (fun v : Native.Line => v.parts) huv
    exact congrArg Subtype.val (a.residueChart.lines.injective he)
  exact ⟨b,lift l l hgl,lift k m hgk⟩

/-- The literal simultaneous point–line stabilizer acts transitively on each
of the five labeled classes; the lifting uses the original Todd projection. -/
theorem orbital_transitive (x : Point a.P) (l k m : Line a.L) (i : Fin 5)
    (hk : LineType a.residueChart i x l k) (hm : LineType a.residueChart i x l m) :
    ∃ g : G, g • x = x ∧ g • l = l ∧ g • k = m := by
  let r := representative x
  have hx : r⁻¹ • x = Cosets.vertex a.P.M 1 := ResidueChart.representative_inv_point x
  have inc (u : Line a.L) (hu : OnLine a.L x u) :
      OnLine a.L (Cosets.vertex a.P.M 1) (r⁻¹ • u) := by
    simpa only [OnLine,hx] using incident_smul r⁻¹ hu
  let l' := (⟨r⁻¹ • l,inc l (lineType_incident hk).1⟩ :
    {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
  let k' := (⟨r⁻¹ • k,inc k (lineType_incident hk).2⟩ :
    {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
  let m' := (⟨r⁻¹ • m,inc m (lineType_incident hm).2⟩ :
    {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
  have hk' : LineType a.residueChart i (Cosets.vertex a.P.M 1) l'.val k'.val := by
    simpa only [hx] using lineType_smul r⁻¹ hk
  have hm' : LineType a.residueChart i (Cosets.vertex a.P.M 1) l'.val m'.val := by
    simpa only [hx] using lineType_smul r⁻¹ hm
  obtain ⟨g,hgl,hgk⟩ := a.orbital_transitive_base l' k' m' i hk' hm'
  refine ⟨r*(g : G)*r⁻¹,?_,?_,?_⟩
  · have hg : (g : G) • Cosets.vertex a.P.M 1 = Cosets.vertex a.P.M 1 := by
      rw [Cosets.smul_vertex,mul_one]
      exact (Cosets.vertex_eq_base _ _).mpr g.property
    rw [mul_smul,mul_smul,hx,hg,←hx,smul_inv_smul]
  · change (g : G) • (r⁻¹ • l) = r⁻¹ • l at hgl
    rw [mul_smul,mul_smul,hgl,smul_inv_smul]
  · change (g : G) • (r⁻¹ • k) = r⁻¹ • m at hgk
    rw [mul_smul,mul_smul,hgk,smul_inv_smul]

/-- The five actual ambient valencies under the original residue chart. -/
theorem delta_card (x : Point a.P) (l : Line a.L) (hl : OnLine a.L x l) (i : Fin 5) :
    {k | LineType a.residueChart i x l k}.ncard =
      (![1,42,56,1008,2688] : Fin 5 → ℕ) i := by
  rw [lineType_card a.residueChart i x ⟨l,hl⟩]
  exact NativeLineOrbit.valency _ i


variable (d : LocalData h)

private theorem incident_lines_transitive {x : Point d.P} {l k : Line d.L}
    (hl : OnLine d.L x l) (hk : OnLine d.L x k) :
    ∃ g : G, g • x = x ∧ g • l = k := by
  obtain ⟨a, hax, hal⟩ := hl
  obtain ⟨b, hbx, hbk⟩ := hk
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · rw [← hax, Cosets.smul_vertex, inv_mul_cancel_right]
    exact hbx.trans hax.symm
  · rw [← hal, Cosets.smul_vertex, inv_mul_cancel_right]
    exact hbk

private theorem lineType_pair_transitive {x : Point d.P} {l k a b : Line d.L} {i : Fin 5}
    (hlk : LineType d.residueChart i x l k) (hab : LineType d.residueChart i x a b) :
    ∃ g : G, g • x = x ∧ g • l = a ∧ g • k = b := by
  obtain ⟨g, hgx, hgl⟩ := d.incident_lines_transitive
    (lineType_incident hlk).1 (lineType_incident hab).1
  have ht : LineType d.residueChart i x a (g • k) := by
    simpa only [hgx, hgl] using lineType_smul g hlk
  obtain ⟨f, hfx, hfa, hfg⟩ := d.orbital_transitive x a (g • k) b i ht hab
  exact ⟨f * g, by rw [mul_smul, hgx, hfx],
    by rw [mul_smul, hgl, hfa], by rw [mul_smul, hfg]⟩

/-- Reversal transports one complete orbital to its paired orbital. -/
private theorem lineType_reverse_orbital {x : Point d.P} {l k : Line d.L} {i j : Fin 5}
    (hlk : LineType d.residueChart i x l k) (hkl : LineType d.residueChart j x k l)
    {a b : Line d.L} (hab : LineType d.residueChart i x a b) :
    LineType d.residueChart j x b a := by
  obtain ⟨g, hgx, hgl, hgk⟩ := d.lineType_pair_transitive hlk hab
  simpa only [hgx, hgl, hgk] using lineType_smul g hkl

/-- The five orbital lengths are distinct, so pairing forces every native
transported orbital to be self-paired. The finite count is symbolic. -/
theorem lineType_symm {x : Point d.P} {l k : Line d.L} {i : Fin 5}
    (hlk : LineType d.residueChart i x l k) : LineType d.residueChart i x k l := by
  classical
  have hxl := (lineType_incident hlk).1
  have hxk := (lineType_incident hlk).2
  obtain ⟨j, hkl, _⟩ := d.orbital_partition x k l hxk hxl
  let X := {a : Line d.L // OnLine d.L x a}
  let valency : Fin 5 → ℕ := ![1,42,56,1008,2688]
  let pairs (t : Fin 5) := Σ a : X, {b : X // LineType d.residueChart t x a.val b.val}
  let swap : pairs i ≃ pairs j :=
    { toFun := fun p => ⟨p.2.val, ⟨p.1, d.lineType_reverse_orbital hlk hkl p.2.property⟩⟩
      invFun := fun p => ⟨p.2.val, ⟨p.1, d.lineType_reverse_orbital hkl hlk p.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let : Fintype X := Fintype.ofFinite X
  have fiber (t : Fin 5) (a : X) :
      Nat.card {b : X // LineType d.residueChart t x a.val b.val} = valency t := by
    let e : {b : X // LineType d.residueChart t x a.val b.val} ≃
        {b : Line d.L // LineType d.residueChart t x a.val b} :=
      { toFun := fun b => ⟨b.val.val, b.property⟩
        invFun := fun b => ⟨⟨b.val, (lineType_incident b.property).2⟩, b.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).trans (d.delta_card x a.val a.property t)
  have card (t : Fin 5) : Nat.card (pairs t) = Nat.card X * valency t := by
    change Nat.card (Σ a : X, {b : X // LineType d.residueChart t x a.val b.val}) = _
    rw [Nat.card_sigma]
    simp only [fiber, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
  have he : Nat.card X * valency i = Nat.card X * valency j := by
    rw [← card i, ← card j]
    exact Nat.card_congr swap
  let : Nonempty X := ⟨⟨l, hxl⟩⟩
  have he' : valency i = valency j := Nat.eq_of_mul_eq_mul_left Nat.card_pos he
  have hij : i = j := by
    fin_cases i <;> fin_cases j <;> first | rfl | norm_num [valency] at he'
  exact hij ▸ hkl

/-- The source line-pair interchange, before the endpoint adjustments in
(5.6): an actual ambient element fixes the point and exchanges its two lines. -/
theorem line_pair_swap {x : Point d.P} {l k : Line d.L} {i : Fin 5}
    (hlk : LineType d.residueChart i x l k) :
    ∃ g : G, g • x = x ∧ g • l = k ∧ g • k = l :=
  d.lineType_pair_transitive hlk (d.lineType_symm hlk)

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
