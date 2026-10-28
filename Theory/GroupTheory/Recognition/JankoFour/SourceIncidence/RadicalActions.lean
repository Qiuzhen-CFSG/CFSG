module
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.TrianglePlanes
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.OrbitTransport
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Orbitals
public import Theory.GroupTheory.Recognition.JankoFour.SourceFusion.Orbits
public import Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.Native.PairSpaces

/-!
# The radical point stabilizer on a second line

The already proved neighboring-radical image lifts every native trio-core
actor to an element fixing all points of the first ambient line. Its
commutators with E therefore fix that line as well. The actual Todd action
identifies their span with the within-octad cocode pair space. For the three
labels greater than one, the two pair spaces span the entire cocode.
Splitting an E-transporter along those spaces gives a transporter fixing the
chosen neighbor, on the original ambient point and line cosets.

Source: Aschbacher–Segev (1991), (5.4)(6), pp.600–601.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
open LocalGeometry LocalGeometry.LocalSubgroups SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z} (a : LocalData h)

noncomputable def vectorLineKernel (l : Line a.L) : Submodule (ZMod 2) Cocode where
  carrier := {v | ∀ y : Point a.P, OnLine a.L y l →
    a.P.vectorEmbedding (Multiplicative.ofAdd v) • y = y}
  zero_mem' := by intro y _; change a.P.vectorEmbedding 1 • y = y; rw [map_one,one_smul]
  add_mem' := by
    intro v w hv hw y hy
    change a.P.vectorEmbedding (Multiplicative.ofAdd v * Multiplicative.ofAdd w) • y = y
    rw [map_mul,mul_smul,hw y hy,hv y hy]
  smul_mem' := by
    intro c v hv
    rcases (by decide : ∀ c : ZMod 2, c=0 ∨ c=1) c with rfl|rfl
    · intro y _; simp only [zero_smul]; change a.P.vectorEmbedding 1 • y = y; rw [map_one,one_smul]
    · simpa only [one_smul] using hv

/-- The literal within-octad cocode space fixes the five points of its
ambient line, through the native image of the neighboring radical. -/
theorem pairSpace_le_vectorLineKernel
    (l : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l}) :
    NativePairSpaces.pairSpace (a.residueChart.lines l) ≤ a.vectorLineKernel l.val := by
  obtain ⟨y,hy,hne⟩ : ∃ y, OnLine a.L y l.val ∧ y ≠ Cosets.vertex a.P.M 1 := by
    by_contra hn
    have hs : {y | OnLine a.L y l.val} ⊆ {Cosets.vertex a.P.M 1} := by
      intro y hy
      by_contra hne
      exact hn ⟨y,hy,hne⟩
    have hc := Set.ncard_le_ncard hs
    rw [a.line_card,Set.ncard_singleton] at hc
    omega
  rw [NativePairSpaces.pairSpace_eq_commutator]
  apply Submodule.span_le.mpr
  rintro _ ⟨g,hg,v,_,rfl⟩
  obtain ⟨r,hr,hq⟩ := (a.neighbor_core_image_of_line l y hy hne).ge hg
  have hfixr : ∀ u, OnLine a.L u l.val → (r : G) • u = u := by
    apply a.core_regular_other y l.val hy ⟨r,hr⟩ (Cosets.vertex a.P.M 1) l.property hne.symm
    rw [Cosets.smul_vertex,mul_one]
    exact (Cosets.vertex_eq_base _ _).mpr r.property
  let e := a.P.vectorEmbedding (Multiplicative.ofAdd v)
  have heE : e ∈ a.P.E := ⟨_,rfl⟩
  have hcore : e⁻¹ ∈ coreAt a.P (Cosets.vertex a.P.M 1) := by
    rw [coreAt_vertex]
    change (1 : G)⁻¹*e⁻¹*((1 : G)⁻¹)⁻¹ ∈ a.P.E
    simpa only [inv_one,one_mul,mul_one] using a.P.E.inv_mem heE
  have hfixe : e⁻¹ • l.val = l.val := a.core_fixes_lines _ ⟨e⁻¹,hcore⟩ l.val l.property
  have hd : a.P.vectorEmbedding (Multiplicative.ofAdd (cocodeRepresentation g v - v)) =
      (r : G)*e*(r : G)⁻¹*e⁻¹ := by
    rw [←hq,ofAdd_sub,map_div,div_eq_mul_inv,←SourceFusion.vector_conj a.P r]
    rfl
  intro u hu
  have hu' : OnLine a.L (e⁻¹ • u) l.val := by
    simpa only [OnLine,hfixe] using incident_smul e⁻¹ hu
  have hrinv : (r : G)⁻¹ • (e⁻¹ • u) = e⁻¹ • u :=
    inv_smul_eq_iff.mpr (hfixr _ hu').symm
  rw [hd,mul_smul,mul_smul,mul_smul,hrinv,smul_inv_smul,hfixr u hu]

private theorem core_stabilizer_transitive_base
    (l k : {l : Line a.L // OnLine a.L (Cosets.vertex a.P.M 1) l})
    (y : Point a.P) (hy : OnLine a.L y l.val) (i : Fin 5) (hi : 1 < i.val)
    (ht : LineType a.residueChart i (Cosets.vertex a.P.M 1) l.val k.val)
    (u v : Point a.P) (hu : OnLine a.L u k.val) (hux : u ≠ Cosets.vertex a.P.M 1)
    (hv : OnLine a.L v k.val) (hvx : v ≠ Cosets.vertex a.P.M 1) :
    ∃ e : a.P.E, (e : G) • y = y ∧ (e : G) • u = v := by
  have ht' := (lineType_base a.residueChart i l k).mp ht
  have hsup : a.vectorLineKernel l.val ⊔ a.vectorLineKernel k.val = ⊤ := by
    apply top_unique
    rw [←NativePairSpaces.sup_eq_top _ _ i hi ht']
    exact sup_le_sup (a.pairSpace_le_vectorLineKernel l) (a.pairSpace_le_vectorLineKernel k)
  obtain ⟨e,he⟩ := a.core_transitive_other (Cosets.vertex a.P.M 1) k.val k.property
    u v hu hux hv hvx
  have heE : (e : G) ∈ a.P.E := by
    have hh := (coreAt_vertex a.P 1).le e.property
    change (1 : G)⁻¹*(e : G)*((1 : G)⁻¹)⁻¹ ∈ a.P.E at hh
    simpa only [inv_one,one_mul,mul_one] using hh
  obtain ⟨w,hw⟩ := heE
  have hw' : w.toAdd ∈ a.vectorLineKernel l.val ⊔ a.vectorLineKernel k.val := by rw [hsup]; trivial
  obtain ⟨p,hp,q,hq,hpq⟩ := Submodule.mem_sup.mp hw'
  refine ⟨⟨a.P.vectorEmbedding (Multiplicative.ofAdd p),⟨_,rfl⟩⟩,hp y hy,?_⟩
  have hh := he
  rw [←hw] at hh
  change a.P.vectorEmbedding (Multiplicative.ofAdd w.toAdd) • u = v at hh
  rw [←hpq] at hh
  change a.P.vectorEmbedding (Multiplicative.ofAdd p * Multiplicative.ofAdd q) • u = v at hh
  rw [map_mul,mul_smul,hq u hu] at hh
  exact hh

/-- AS91 (5.4)(6), with the actual stabilizer inside the original point
radical, for all three labels greater than one. -/
theorem core_stabilizer_transitive (x y : Point a.P) (l k : Line a.L) (i : Fin 5)
    (hxl : OnLine a.L x l) (hyl : OnLine a.L y l) (_hyx : y ≠ x)
    (hi : 1 < i.val) (ht : LineType a.residueChart i x l k)
    (u v : Point a.P) (hu : OnLine a.L u k) (hux : u ≠ x)
    (hv : OnLine a.L v k) (hvx : v ≠ x) :
    ∃ e : coreAt a.P x, (e : G) • y = y ∧ (e : G) • u = v := by
  let r := representative x
  have hx : r⁻¹ • x = Cosets.vertex a.P.M 1 := ResidueChart.representative_inv_point x
  have inc (s : Line a.L) (hs : OnLine a.L x s) :
      OnLine a.L (Cosets.vertex a.P.M 1) (r⁻¹ • s) := by
    simpa only [OnLine,hx] using incident_smul r⁻¹ hs
  have neq (v : Point a.P) (hv : v ≠ x) : r⁻¹ • v ≠ Cosets.vertex a.P.M 1 := by
    rw [←hx]
    exact (MulAction.injective r⁻¹).ne hv
  obtain ⟨e,hey,heu⟩ := a.core_stabilizer_transitive_base
    ⟨r⁻¹ • l,inc l hxl⟩ ⟨r⁻¹ • k,inc k (lineType_incident ht).2⟩
    (r⁻¹ • y) (incident_smul r⁻¹ hyl) i hi
    (by simpa only [hx] using lineType_smul r⁻¹ ht)
    (r⁻¹ • u) (r⁻¹ • v) (incident_smul r⁻¹ hu) (neq u hux)
    (incident_smul r⁻¹ hv) (neq v hvx)
  have hm : r*(e : G)*r⁻¹ ∈ coreAt a.P x := by
    rw [←vertex_representative x,coreAt_vertex]
    change r⁻¹*(r*(e : G)*r⁻¹)*(r⁻¹)⁻¹ ∈ a.P.E
    simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using e.property
  exact ⟨⟨r*(e : G)*r⁻¹,hm⟩,by rw [mul_smul,mul_smul,hey,smul_inv_smul],
    by rw [mul_smul,mul_smul,heu,smul_inv_smul]⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.LocalData
