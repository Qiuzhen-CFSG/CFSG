module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Statements

/-!
# Literal quotient fibers and remaining J.2.8 geometry

Conjugation by H preserves HC and Q, so it induces an automorphism of the
actual quotient Q/HC. The involution fibers retain their representatives in Q.
The seed records U_alpha = ell U ell^-1 and w in U_alpha intersect Q minus HC;
its construction is proved in `Seed` from the earlier J.2.2–3 clauses.

`FiberGeometry`, `QuotientTransport` and `ElementaryTransport` are explicit
remaining proof obligations, not source hypotheses or proved book theorems.
Their constructors must be supplied before the conditional assembly in
`Fusion.CoreOrbit` establishes J.2.8 from earlier source results.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.8, printed pp.437–438 (PDF pp.448–449 of `refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]

private def conjugationOn (A H : Subgroup G) (hn : H ≤ normalizer A) (h : H) : MulAut A :=
  A.normalizerMonoidHom ⟨h, hn h.property⟩

omit [Finite G] in
private theorem conjugationOn_mem_iff (A H N : Subgroup G) (hn : H ≤ normalizer A)
    (hN : H ≤ normalizer N) (h : H) (x : A) :
    (conjugationOn A H hn h x : G) ∈ N ↔ (x : G) ∈ N :=
  (mem_normalizer_iff.mp (hN h.property) x).symm

theorem centralizer_normalized (d : TypeRuSetup G) : d.H ≤ normalizer d.HC := by
  apply le_normalizer_iff.mpr
  intro h hh c hc
  refine ⟨d.H.mul_mem (d.H.mul_mem hh hc.1) (d.H.inv_mem hh), ?_⟩
  intro u hu
  have hu' : h⁻¹ * u * h ∈ d.U := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (d.ru2.natural.normalized (d.H.inv_mem hh)) u).mp hu
  have he := congrArg (fun a : G => h * a * h⁻¹) (hc.2 _ hu')
  simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel,
    mul_one] using he

instance coreKernelNormal (d : TypeRuSetup G) : (d.HC.subgroupOf d.Q).Normal := by
  refine ⟨?_⟩
  intro a ha q
  change (q : G) * (a : G) * (q : G)⁻¹ ∈ d.HC
  exact (mem_normalizer_iff.mp
    (centralizer_normalized d (pCoreIn_le 2 d.H q.property)) a).mp ha

/-- The literal quotient Q/(HC intersect Q), with relative normality proved above. -/
abbrev CoreQuotient (d : TypeRuSetup G) := d.Q ⧸ d.HC.subgroupOf d.Q

/-- The canonical quotient homomorphism from Q. -/
def coreMap (d : TypeRuSetup G) : d.Q →* CoreQuotient d := QuotientGroup.mk' _

/-- Equality of quotient coordinates is membership in the literal left coset y HC. -/
theorem coreMap_eq_iff (d : TypeRuSetup G) (x y : d.Q) :
    coreMap d x = coreMap d y ↔ (y : G)⁻¹ * x ∈ d.HC :=
  eq_comm.trans QuotientGroup.eq

/-- Actual conjugation of Q by an element of H. -/
def coreConj (d : TypeRuSetup G) (h : d.H) : MulAut d.Q :=
  d.Q.normalizerMonoidHom ⟨h, d.ru2.six.normalized h.property⟩

theorem coreConj_kernel (d : TypeRuSetup G) (h : d.H) :
    (d.HC.subgroupOf d.Q).map (coreConj d h) = d.HC.subgroupOf d.Q := by
  ext x
  change x ∈ (d.HC.subgroupOf d.Q).map (coreConj d h).toMonoidHom ↔ _
  rw [mem_map_equiv]
  change ((coreConj d h).symm x : G) ∈ d.HC ↔ (x : G) ∈ d.HC
  have he := conjugationOn_mem_iff d.Q d.H d.HC d.ru2.six.normalized
    (centralizer_normalized d) h ((coreConj d h).symm x)
  change (coreConj d h ((coreConj d h).symm x) : G) ∈ d.HC ↔
    ((coreConj d h).symm x : G) ∈ d.HC at he
  simpa only [MulEquiv.apply_symm_apply] using he.symm

/-- The action induced by the actual conjugator on Q/HC. -/
def quotientConj (d : TypeRuSetup G) (h : d.H) : MulAut (CoreQuotient d) :=
  QuotientGroup.congr _ _ (coreConj d h) (coreConj_kernel d h)

theorem quotientConj_mk (d : TypeRuSetup G) (h : d.H) (x : d.Q) :
    quotientConj d h (coreMap d x) = coreMap d (coreConj d h x) := rfl

/-- Involutions in one fiber of the literal quotient map. -/
def fiber (d : TypeRuSetup G) (a : CoreQuotient d) : Set d.Q :=
  {x | coreMap d x = a ∧ orderOf (x : G) = 2}

/-- A chosen L-conjugate of U and an element of its intersection with Q outside HC. -/
structure ConjugateSeed (d : TypeRuSetup G) where
  ell : d.L
  w : d.Q
  mem_conjugate : (w : G) ∈ d.U.map (MulAut.conj (ell : G)).toMonoidHom
  outside : (w : G) ∉ d.HC

def seedCentralizer (d : TypeRuSetup G) (s : ConjugateSeed d) : Subgroup G :=
  d.U ⊓ centralizer ({(s.w : G)} : Set G)

/-- Remaining algebraic obligations in the first two paragraphs of J.2.8.
The involution equation specifies precisely the set w C_U(w); `conjugate`
requires an actual element of Q for each member of this set. This record
has no constructor here: its fields must be proved from J.2.1–4 and J.2.6. -/
structure FiberGeometry (d : TypeRuSetup G) (s : ConjugateSeed d) : Prop where
  involutions : ∀ x : d.Q, x ∈ fiber d (coreMap d s.w) ↔
    (s.w : G)⁻¹ * x ∈ seedCentralizer d s
  centralizer_card : Nat.card (seedCentralizer d s) = 16
  conjugate : ∀ x : fiber d (coreMap d s.w),
    ∃ q : d.Q, (q : G) * s.w * (q : G)⁻¹ = x
  centralizer_control : ∃ v ∈ seedCentralizer d s, v ∉ d.V ∧
    d.S ⊓ centralizer ({v} : Set G) ≤ d.Q

/-- The natural quotient action and its restriction to the parabolic overlap.
The restricted assertion concerns all nonzero cosets of S intersect Q and
retains its conjugator in L intersect H. It is not a hypothesis of type Ru. -/
structure QuotientTransport (d : TypeRuSetup G) (s : ConjugateSeed d) : Prop where
  card : Nat.card (CoreQuotient d) = 16
  all : ∀ a : CoreQuotient d, a ≠ 1 →
    ∃ h : d.H, quotientConj d h (coreMap d s.w) = a
  parabolic : ∀ x : d.Q, (x : G) ∈ d.S → (x : G) ∉ d.HC →
    ∃ l : (d.L ⊓ d.H : Subgroup G),
      quotientConj d ⟨l, l.property.2⟩ (coreMap d s.w) = coreMap d x

/-- The earlier-action consequence that L fuses the elements of U minus V.
Constructing this proposition remains an obligation of the transport branch. -/
def ElementaryTransport (d : TypeRuSetup G) : Prop :=
  ∀ u v : G, u ∈ d.U → u ∉ d.V → v ∈ d.U → v ∉ d.V →
    ∃ l : d.L, (l : G) * u * (l : G)⁻¹ = v


end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
