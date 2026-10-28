module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortCentralizer
import all CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortCentralizer

/-!
# Involution fusion through the same general Ree extension

Every involution of the full normalizer extension lies in its native inner
subgroup, since the outer degree is odd. The native octagon has a connected
fixed graph for its cyclic two-subgroup, and the marked graph isomorphism
transports this graph to the extension. Along a fixed path, a common coset
representative for each adjacent pair identifies the conjugated element in
both endpoints. Compatible endpoint homomorphisms therefore preserve its
conjugacy class, even without a homomorphism from the entire extension.

This proves the involution specialization of F.4.30 used in F.4.35, from
the model extension to the original completion. The source also treats
arbitrary subsets; that stronger statement is not asserted here. Converse
fusion, two-class exhaustion and ambient short-centralizer containment remain. The
internal import reuses the established native graph comparison.
Source: Aschbacher–Smith F.4.30,35,40–43, printed pp.290–296
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry SimpleGraph
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
namespace Fusion
variable {N G : Type*} [Group N] [Group G]
variable (F : Bool → Subgroup N) (f : ∀ i, F i →* G)

private theorem conjugate_mem {x : N} {v : CosetGeometry.Vertex F}
    (hv : x • v = v) (g : N) (hg : g • CosetGeometry.base F v.type = v) :
    g⁻¹*x*g ∈ F v.type := by
  rw [←CosetGeometry.stabilizer_base F v.type]
  change (g⁻¹*x*g) • CosetGeometry.base F v.type = _
  rw [mul_smul,mul_smul,hg,hv,←hg,inv_smul_smul]
  rfl

private theorem representatives {x : N} {v : CosetGeometry.Vertex F}
    (hv : x • v = v) (g h : N)
    (hg : g • CosetGeometry.base F v.type = v)
    (hh : h • CosetGeometry.base F v.type = v) :
    IsConj (f v.type ⟨g⁻¹*x*g,conjugate_mem F hv g hg⟩)
      (f v.type ⟨h⁻¹*x*h,conjugate_mem F hv h hh⟩) := by
  have ha : h⁻¹*g ∈ F v.type := by
    rw [←CosetGeometry.stabilizer_base F v.type]
    change (h⁻¹*g) • CosetGeometry.base F v.type = _
    rw [mul_smul,hg,←hh,inv_smul_smul]
    rfl
  apply isConj_iff.mpr
  refine ⟨f v.type ⟨h⁻¹*g,ha⟩,?_⟩
  rw [←map_inv,←map_mul,←map_mul]
  apply congrArg (f v.type)
  apply Subtype.ext
  change (h⁻¹*g)*(g⁻¹*x*g)*(h⁻¹*g)⁻¹ = h⁻¹*x*h
  group

private def representative (v : CosetGeometry.Vertex F) : N :=
  Classical.choose (CosetGeometry.exists_smul_base F v)

private theorem representative_spec (v : CosetGeometry.Vertex F) :
    representative F v • CosetGeometry.base F v.type = v :=
  Classical.choose_spec (CosetGeometry.exists_smul_base F v)

private def label (x : N) (v : {v : CosetGeometry.Vertex F // x • v = v}) : G :=
  f v.val.type ⟨(representative F v.val)⁻¹*x*representative F v.val,
    conjugate_mem F v.property _ (representative_spec F v.val)⟩

private theorem label_conj (x : N) (v : {v : CosetGeometry.Vertex F // x • v = v})
    (g : N) (hg : g • CosetGeometry.base F v.val.type = v.val) :
    IsConj (label F f x v) (f v.val.type ⟨g⁻¹*x*g,conjugate_mem F v.property g hg⟩) :=
  representatives F f v.property _ _ (representative_spec F v.val) hg

private theorem label_adjacent (x : N)
    (hc : ∀ (y : N) (h₀ : y ∈ F false) (h₁ : y ∈ F true),
      f false ⟨y,h₀⟩ = f true ⟨y,h₁⟩)
    {v w : {v : CosetGeometry.Vertex F // x • v = v}}
    (ha : ((CosetGeometry.RankTwo.graph F).induce {v | x • v = v}).Adj v w) :
    IsConj (label F f x v) (label F f x w) := by
  obtain ⟨g,hg,hh⟩ := CosetGeometry.RankTwo.incident_common_translate F ha.2
  have he : f v.val.type ⟨g⁻¹*x*g,conjugate_mem F v.property g hg⟩ =
      f w.val.type ⟨g⁻¹*x*g,conjugate_mem F w.property g hh⟩ := by
    have compat (i j : Bool) (z : N) (hi : z ∈ F i) (hj : z ∈ F j) :
        f i ⟨z,hi⟩ = f j ⟨z,hj⟩ := by
      cases i <;> cases j
      · rfl
      · exact hc _ _ _
      · exact (hc _ _ _).symm
      · rfl
    exact compat _ _ _ _ _
  exact (label_conj F f x v g hg).trans (he ▸ (label_conj F f x w g hh).symm)

private theorem label_connected (x : N)
    (hc : ∀ (y : N) (h₀ : y ∈ F false) (h₁ : y ∈ F true),
      f false ⟨y,h₀⟩ = f true ⟨y,h₁⟩)
    (hconn : ((CosetGeometry.RankTwo.graph F).induce {v | x • v = v}).Preconnected)
    (v w : {v : CosetGeometry.Vertex F // x • v = v}) :
    IsConj (label F f x v) (label F f x w) := by
  obtain ⟨p⟩ := hconn v w
  induction p with
  | nil => exact IsConj.refl _
  | cons ha p ih => exact (label_adjacent F f x hc ha).trans ih

/-- A connected fixed graph transfers endpoint fusion through compatible maps. -/
theorem of_fixed_connected
    (hc : ∀ (y : N) (h₀ : y ∈ F false) (h₁ : y ∈ F true),
      f false ⟨y,h₀⟩ = f true ⟨y,h₁⟩)
    {i j : Bool} (x : F i) (y : F j)
    (hconn : ((CosetGeometry.RankTwo.graph F).induce {v | x.val • v = v}).Preconnected)
    (hxy : IsConj x.val y.val) : IsConj (f i x) (f j y) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  have hx : x.val • CosetGeometry.base F i = CosetGeometry.base F i := by
    change x.val ∈ MulAction.stabilizer N (CosetGeometry.base F i)
    rw [CosetGeometry.stabilizer_base]
    exact x.property
  have hy : y.val • CosetGeometry.base F j = CosetGeometry.base F j := by
    change y.val ∈ MulAction.stabilizer N (CosetGeometry.base F j)
    rw [CosetGeometry.stabilizer_base]
    exact y.property
  have hy' : x.val • (g⁻¹ • CosetGeometry.base F j) = g⁻¹ • CosetGeometry.base F j := by
    apply (MulAction.toPerm g).injective
    change g • (x.val • (g⁻¹ • CosetGeometry.base F j)) = g • (g⁻¹ • CosetGeometry.base F j)
    rw [smul_inv_smul,←mul_smul,←mul_smul]
    have he : g*x.val*g⁻¹ = y.val := hg
    rw [he]
    exact hy
  let v : {v : CosetGeometry.Vertex F // x.val • v = v} := ⟨CosetGeometry.base F i,hx⟩
  let w : {v : CosetGeometry.Vertex F // x.val • v = v} := ⟨g⁻¹ • CosetGeometry.base F j,hy'⟩
  have h₀ := label_conj F f x.val v 1 (one_smul _ _)
  have h₁ := label_conj F f x.val w g⁻¹ rfl
  have h₀' : IsConj (label F f x.val v) (f i x) := by
    convert h₀ using 1
    exact congrArg (f i) (Subtype.ext (by simp))
  have h₁' : IsConj (label F f x.val w) (f j y) := by
    convert h₁ using 1
    exact congrArg (f j) (Subtype.ext (by simpa only [inv_inv] using hg.symm))
  exact h₀'.symm.trans ((label_connected F f x.val hc hconn v w).trans h₁')

end Fusion
open GroupAction.EvenPolygon ReeF4 ReeF4.Parabolics
open ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
variable {m : ℕ} (E : GeneralReeExtension.SourceExtension m)

/-- Every involution of the full extension comes from the native inner group. -/
theorem extension_involution_native (hm : 0 < m) (x : E.carrier) (hx : orderOf x = 2) :
    ∃ t : Model m, orderOf t = 2 ∧ E.baseHom t = x := by
  have hr : x ∈ primeToResidual 2 E.carrier := mem_primeToResidual_of_pow (n := 1)
    (by simpa only [pow_one,hx] using pow_orderOf_eq_one x)
  rw [ReeF4.SourceCompletion.extension_primeToResidual hm E.carrier E.contains_inner] at hr
  obtain ⟨t,ht⟩ := hr
  have ht' : E.baseHom t = x := Subtype.ext ht
  have hi : Function.Injective E.baseHom :=
    (MonoidHom.injective_codRestrict _ _ _).mpr (ReeF4.SmallCompletion.conj_injective m hm)
  exact ⟨t,((orderOf_injective E.baseHom hi t).symm.trans (ht' ▸ hx)),ht'⟩

/-- The full extension involution fixes a connected subgraph in the same octagon. -/
theorem extension_involution_fixed_connected (hm : 0 < m)
    (x : E.carrier) (hx : orderOf x = 2) :
    ((CosetGeometry.RankTwo.graph E.family).induce {v | x • v = v}).Connected := by
  obtain ⟨t,ht,rfl⟩ := extension_involution_native E hm x hx
  obtain ⟨f,_,hfs⟩ := native_graph_comparison m
  have hi := ReeF4.SmallCompletion.conj_injective m hm
  let e : incidenceGraph m ≃g CosetGeometry.RankTwo.graph E.family := f.trans (E.graphIso hi)
  have es (g : Model m) (v) : e (g • v) = E.baseHom g • e v :=
    (congrArg (E.vertexMap hi) (hfs g v)).trans (E.vertexMap_smul hi g (f v))
  have fix (v) : v ∈ fixedVertices (zpowers t) ↔ E.baseHom t • e v = e v := by
    constructor
    · intro hv
      rw [←es,hv t (mem_zpowers t)]
    · intro hv r hr
      have hh : zpowers t ≤ MulAction.stabilizer (Model m) v :=
        zpowers_le.mpr (e.injective ((es t v).trans hv))
      exact hh hr
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,ht,pow_one])
  have hconn := fixed_graph_connected
    ((octagonGeometry m hm).toEvenPolygonAction (oddApartmentStabilizers m hm))
    (zpowers t) (ConverseParabolics.twoSubgroup_fixes_edge _ hp)
  have hb : Set.BijOn e (fixedVertices (zpowers t)) {v | E.baseHom t • v = v} := by
    refine ⟨fun v hv => (fix v).mp hv,e.injective.injOn,?_⟩
    intro v hv
    refine ⟨e.symm v,(fix _).mpr ?_,e.apply_symm_apply v⟩
    change E.baseHom t • v = v at hv
    simpa only [e.apply_symm_apply] using hv
  exact hconn.map (SimpleGraph.Iso.induce e hb).toHom (SimpleGraph.Iso.induce e hb).surjective

/-- The involution specialization of F.4.30 for the general Ree extension: compatible full endpoint maps preserve involution fusion. -/
theorem extension_involution_fusion (hm : 0 < m)
    {G : Type*} [Group G] (f : ∀ i, E.family i →* G)
    (hc : ∀ (y : E.carrier) (h₀ : y ∈ E.family false) (h₁ : y ∈ E.family true),
      f false ⟨y,h₀⟩ = f true ⟨y,h₁⟩)
    {i j : Bool} (x : E.family i) (y : E.family j)
    (hx : orderOf x.val = 2) (hxy : IsConj x.val y.val) :
    IsConj (f i x) (f j y) :=
  Fusion.of_fixed_connected E.family f hc x y
    (extension_involution_fixed_connected E hm x.val hx).preconnected hxy

end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
