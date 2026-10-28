module
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Separated graph quotients and their group kernels

An invariant equivalence on the vertices gives a genuine permutation action on
its classes and a normal subgroup of the original acting group. Separation at
distance at most two propagates fixation along walks. For a faithful connected
graph action the kernel therefore meets every vertex stabilizer trivially.
The same separation proves that the images of two adjacent stabilizers have
exactly the image of their full intersection as overlap. This last conclusion
does not follow just from the two trivial kernel intersections.

The acting group need not be finite. Finiteness of the class set makes its
quotient by the constructed kernel finite by the first isomorphism theorem.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
Part II, proof of (3.6), printed pp.77--78. The geometric separation is an
explicit input here; apartment uniqueness and exchange must establish it.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
universe u v
variable {X : Type u} {V : Type v} [Group X] [MulAction X V]

/-- Invariance of a vertex equivalence under the original action. -/
def Invariant (r : Setoid V) : Prop :=
  ∀ (g : X) {a b : V}, r a b → r (g • a) (g • b)

variable (r : Setoid V) (hr : Invariant (X := X) r)

/-- The induced action on equivalence classes. -/
@[instance_reducible] def quotientMulAction (r : Setoid V) (hr : Invariant (X := X) r) :
    MulAction X (Quotient r) where
  smul g := @Quotient.map V V r r (g • ·) (fun {_ _} h => hr g h)
  one_smul q := Quotient.inductionOn q (fun a => congrArg (Quotient.mk r) (one_smul X a))
  mul_smul g h q := Quotient.inductionOn q
    (fun a => congrArg (Quotient.mk r) (mul_smul g h a))

/-- The actual induced permutation action on equivalence classes. -/
def quotientAction (r : Setoid V) (hr : Invariant (X := X) r) :
    X →* Equiv.Perm (Quotient r) :=
  @MulAction.toPermHom X (Quotient r) _ (quotientMulAction r hr)

@[simp] theorem quotientAction_mk (g : X) (a : V) :
    quotientAction r hr g (Quotient.mk r a) = Quotient.mk r (g • a) := rfl

/-- Kernel on the quotient vertices, not the original graph kernel. -/
def quotientKernel : Subgroup X := (quotientAction r hr).ker

instance quotientKernel_normal : (quotientKernel r hr).Normal :=
  inferInstanceAs (quotientAction r hr).ker.Normal

theorem mem_quotientKernel (g : X) :
    g ∈ quotientKernel r hr ↔ ∀ a : V, r (g • a) a := by
  constructor
  · intro hg a
    exact Quotient.exact (DFunLike.congr_fun hg (Quotient.mk r a))
  · intro hg
    apply Equiv.ext
    intro q
    induction q using Quotient.inductionOn with
    | h a => exact Quotient.sound (hg a)

variable (Γ : SimpleGraph V)

/-- Separation of distinct equivalent vertices below the indicated distance. -/
def Separated (m : ℕ) : Prop :=
  ∀ {a b : V}, r a b → Γ.dist a b < m → a = b

variable {r Γ}

/-- An element in the quotient kernel fixing a vertex fixes all its neighbors.
This is the local propagation step in DGS (3.6). -/
theorem quotientKernel_fixes_neighbor
    (hconn : Γ.Connected)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {m : ℕ} (hsep : Separated r Γ m) (hm : 2 < m)
    {g : X} (hg : g ∈ quotientKernel r hr) {a b : V}
    (ha : g • a = a) (hab : Γ.Adj a b) : g • b = b := by
  apply hsep ((mem_quotientKernel r hr g).mp hg b)
  have hgb : Γ.Adj a (g • b) := by simpa only [ha] using hact g hab
  have hd := hconn.dist_triangle (u := g • b) (v := a) (w := b)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hgb.symm, SimpleGraph.dist_eq_one_iff_adj.mpr hab] at hd
  exact lt_of_le_of_lt hd hm

/-- Connectedness propagates that fixation to the whole original graph. -/
theorem quotientKernel_fixes_all_of_fixes
    (hconn : Γ.Connected)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {m : ℕ} (hsep : Separated r Γ m) (hm : 2 < m)
    {g : X} (hg : g ∈ quotientKernel r hr) {a : V} (ha : g • a = a)
    (b : V) : g • b = b := by
  obtain ⟨p⟩ := hconn a b
  induction p with
  | nil => exact ha
  | @cons a c b hac p ih =>
    apply ih
    exact quotientKernel_fixes_neighbor hr hconn hact hsep hm hg ha hac

/-- The quotient kernel meets every original vertex stabilizer trivially. -/
theorem quotientKernel_inf_stabilizer [FaithfulSMul X V]
    (hconn : Γ.Connected)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {m : ℕ} (hsep : Separated r Γ m) (hm : 2 < m) (a : V) :
    quotientKernel r hr ⊓ MulAction.stabilizer X a = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  change g = 1
  apply (faithfulSMul_iff.mp (inferInstance : FaithfulSMul X V)) g
  exact quotientKernel_fixes_all_of_fixes hr hconn hact hsep hm hg.1 hg.2

/-- Equality in the actual group quotient gives equivalence of the two
images of every original vertex. -/
theorem related_of_quotient_eq {g h : X}
    (he : QuotientGroup.mk' (quotientKernel r hr) g =
      QuotientGroup.mk' (quotientKernel r hr) h) (a : V) :
    r (g • a) (h • a) := by
  have he' : quotientAction r hr g = quotientAction r hr h :=
    congrArg (QuotientGroup.kerLift (quotientAction r hr)) he
  exact Quotient.exact (DFunLike.congr_fun he' (Quotient.mk r a))

/-- The same geometric separation preserves the whole intersection of
adjacent stabilizers. Trivial intersections with the kernel alone would not. -/
theorem map_stabilizer_inf (hconn : Γ.Connected)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {m : ℕ} (hsep : Separated r Γ m) (hm : 2 < m) {a b : V} (hab : Γ.Adj a b) :
    (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b).map
        (QuotientGroup.mk' (quotientKernel r hr)) =
      (MulAction.stabilizer X a).map (QuotientGroup.mk' (quotientKernel r hr)) ⊓
        (MulAction.stabilizer X b).map (QuotientGroup.mk' (quotientKernel r hr)) := by
  apply le_antisymm (Subgroup.map_inf_le _ _ _)
  rintro z ⟨⟨g, hga, rfl⟩, ⟨h, hhb, he⟩⟩
  have hrel := related_of_quotient_eq hr he.symm b
  change h • b = b at hhb
  rw [hhb] at hrel
  have hgb : g • b = b := by
    apply hsep hrel
    have hadj : Γ.Adj a (g • b) := by
      simpa only [show g • a = a from hga] using hact g hab
    have hd := hconn.dist_triangle (u := g • b) (v := a) (w := b)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm,
      SimpleGraph.dist_eq_one_iff_adj.mpr hab] at hd
    exact lt_of_le_of_lt hd hm
  exact ⟨g, ⟨hga, hgb⟩, rfl⟩

/-- Restricting the one quotient map to an original vertex stabilizer is
injective; there is no global injectivity hypothesis. -/
theorem quotient_injective_on_stabilizer [FaithfulSMul X V]
    (hconn : Γ.Connected)
    (hact : ∀ (g : X) {a b : V}, Γ.Adj a b → Γ.Adj (g • a) (g • b))
    {m : ℕ} (hsep : Separated r Γ m) (hm : 2 < m) (a : V) :
    Function.Injective (fun g : MulAction.stabilizer X a =>
      QuotientGroup.mk' (quotientKernel r hr) (g : X)) := by
  intro g h he
  apply Subtype.ext
  have hker : (g : X)⁻¹ * h ∈ quotientKernel r hr :=
    QuotientGroup.eq.mp he
  have hfix : (g : X)⁻¹ * h ∈ MulAction.stabilizer X a :=
    (MulAction.stabilizer X a).mul_mem
      ((MulAction.stabilizer X a).inv_mem g.property) h.property
  have hbot : (g : X)⁻¹ * h ∈ quotientKernel r hr ⊓ MulAction.stabilizer X a :=
    ⟨hker, hfix⟩
  rw [quotientKernel_inf_stabilizer hr hconn hact hsep hm a] at hbot
  exact inv_mul_eq_one.mp hbot

/-- Finiteness of the class set makes the genuine group quotient finite,
even when the original acting group is infinite. -/
theorem finite_quotient [Finite (Quotient r)] :
    Finite (X ⧸ quotientKernel r hr) := by
  exact Finite.of_injective (QuotientGroup.kerLift (quotientAction r hr))
    (QuotientGroup.kerLift_injective (quotientAction r hr))

end Theory.GroupTheory.WeakBNPair.RegularTree
