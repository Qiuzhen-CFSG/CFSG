module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ParabolicLift
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.FamilyAction
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import Theory.GroupTheory.SetStrongClosure
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# The three marked offender conjugates in the line radical

We prove the B.4.6 application in 14.7.57(3), retaining the full G₂(2)
and its actual natural or Weyl action. The subgroup A* is the pointwise
centralizer of the span of the three doubly singular lines through the
marked point. The final transport preserves this very subspace in the
original source module, and uses the literal map H → H/O₂(H).
Lean uses left conjugation gAg⁻¹, the inverse of the book's convention.

The numbering changes between the two passages: Chapter 14's M₁*, R₁*
are B.4.6's P₂, R₂. If A₁^g lies in R₂, then Z₂ centralizes Z₁^g.
Since C_L(Z₁)=R₁ and Z₁ is strongly closed in R₁, Z₂^(g⁻¹) lies in Z₁.
The P₁-transitivity on long-root groups inside Z₁ corrects g to a member
of N_L(Z₂)=P₂. Normalizing Z₁ also normalizes C_L(C_V(Z₁))=A₁, so this
correction preserves the offender conjugate. The Borel index three bounds
the orbit. An orbit of size one would make J(T,V)=A₁, contradicting
J(T,V)=R₂ and their orders 8 and 32.

`B46Premises` lists the precise earlier source inputs still to be supplied
by `qt-b-04-g2` and assembled by `qt-14-07-g2-local-parabolics`. Its
strong-closure formulation uses the equality C_L(Z₁)=R₁ from the proof
of B.4.6(11). The root-fusion input is the P₁-transitivity used in the
proof of B.4.6(13); it assumes no orbit or transitivity of offenders.
The equality C_V(Z₁)=Ũ(V₁,V₂)+C_V(L) includes the scalar line in the
Weyl case. No J(R₁,V) input is needed by this deduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.6,
printed pp.88–90, especially its proof of (13), and 14.7.55(4),
14.7.57(3), printed pp.1066–1067. The concrete octonion models are the
existing attributed ATLAS ports imported by `Models`; no source is copied
from ATLAS here.
-/

@[expose] public noncomputable section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
variable {G : Type*} [Group G]

private theorem conj_mul (A : Subgroup G) (g h : G) :
    conjugate A (g * h) = conjugate (conjugate A h) g := by
  rw [conjugate, conjugate, map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem conj_one (A : Subgroup G) : conjugate A 1 = A := by
  change A.map (MulAut.conj 1).toMonoidHom = A
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, map_id]

private theorem conj_inv (A : Subgroup G) (g : G) :
    conjugate (conjugate A g⁻¹) g = A := by
  rw [← conj_mul, mul_inv_cancel, conj_one]

/-- Strong closure turns containment in the line radical into root incidence. -/
private theorem root_incidence (Z₁ Z₂ A R : Subgroup G)
    (hZA : Z₁ ≤ A) (hZZ : Z₂ ≤ Z₁)
    (hstrong : Theory.GroupTheory.IsStronglyClosedSet (Z₁ : Set G)
      (centralizer (Z₁ : Set G)) ⊤)
    (hcentral : R ≤ centralizer (Z₂ : Set G))
    (g : G) (hg : conjugate A g ≤ R) :
    conjugate Z₂ g⁻¹ ≤ Z₁ := by
  rintro _ ⟨z,hz,rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  apply hstrong.2 z (hZZ hz) g (mem_top g)
  intro x hx
  have hmem : g * x * g⁻¹ ∈ R := hg (mem_map_of_mem _ (hZA hx))
  have he := hcentral hmem z hz
  have he' := congrArg (fun y : G => g⁻¹ * y * g) he
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using he'.symm

/-- The root transporter corrects the offender conjugator inside the actual
normalizer of Z₂. The only transitivity input concerns long-root groups in Z₁. -/
private theorem offender_fusion (Z₁ Z₂ A R : Subgroup G)
    (hZA : Z₁ ≤ A) (hZZ : Z₂ ≤ Z₁)
    (hstrong : Theory.GroupTheory.IsStronglyClosedSet (Z₁ : Set G)
      (centralizer (Z₁ : Set G)) ⊤)
    (hcentral : R ≤ centralizer (Z₂ : Set G))
    (hAN : normalizer (Z₁ : Set G) ≤ normalizer (A : Set G))
    (hroot : ∀ g : G, conjugate Z₂ g ≤ Z₁ →
      ∃ n ∈ normalizer (Z₁ : Set G), conjugate Z₂ n = conjugate Z₂ g)
    (g : G) (hg : conjugate A g ≤ R) :
    ∃ c ∈ normalizer (Z₂ : Set G), conjugate A c = conjugate A g := by
  obtain ⟨n,hn,he⟩ := hroot g⁻¹ (root_incidence Z₁ Z₂ A R hZA hZZ hstrong hcentral g hg)
  refine ⟨g * n, mem_normalizer_iff_map_conj_eq.mpr ?_, ?_⟩
  · change conjugate Z₂ (g * n) = Z₂
    rw [conj_mul, he, conj_inv]
  · rw [conj_mul]
    have hnA : conjugate A n = A := mem_normalizer_iff_map_conj_eq.mp (hAN hn)
    rw [hnA]

private noncomputable instance conjugationAction : MulAction G (Subgroup G) :=
  MulAction.compHom (Subgroup G) ConjAct.toConjAct.toMonoidHom

private theorem family_card (A P : Subgroup G) :
    (conjugateLineFamily A P).ncard = (normalizer (A : Set G)).relIndex P := by
  have hf : conjugateLineFamily A P = MulAction.orbit P A := by
    ext B
    exact Iff.rfl
  have hs : MulAction.stabilizer P A = (normalizer (A : Set G)).subgroupOf P := by
    ext g
    exact conjAct_pointwise_smul_iff
  rw [hf, ← MulAction.index_stabilizer, hs]
  rfl

open Representation.BinaryOffender
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Index three and the genuine Thompson generation force the nontrivial
parabolic orbit to have three members. -/
private theorem count_from_generation (ρ : Representation (ZMod 2) G V)
    (A T P R : Subgroup G)
    (hAR : A ≤ R)
    (hTN : T ≤ normalizer (A : Set G)) (hindex : T.relIndex P = 3)
    (hP : ∀ B, IsBestOffender ρ B ↔ ∃ g : G, conjugate A g = B)
    (hJ : generatedBy {B | IsBestOffender ρ B} T = R)
    (hne : R ≠ A)
    (hfusion : ∀ g : G, conjugate A g ≤ R →
      ∃ c ∈ P, conjugate A c = conjugate A g) :
    (conjugateLineFamily A P).ncard = 3 := by
  rw [family_card]
  have hd : (normalizer (A : Set G)).relIndex P ∣ 3 := by
    rw [← hindex]
    exact relIndex_dvd_of_le_left P hTN
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · have hPN : P ≤ normalizer (A : Set G) := relIndex_eq_one.mp h1
    apply (hne (le_antisymm ?_ hAR)).elim
    rw [← hJ]
    apply iSup_le
    intro B
    apply iSup_le
    rintro ⟨hB,hBT⟩
    obtain ⟨g,rfl⟩ := (hP B).mp hB
    have hBR : conjugate A g ≤ R := by
      rw [← hJ]
      exact le_iSup_of_le (conjugate A g) (le_iSup_of_le ⟨hB,hBT⟩ le_rfl)
    obtain ⟨c,hc,he⟩ := hfusion g hBR
    have hcA : conjugate A c = A := mem_normalizer_iff_map_conj_eq.mp (hPN hc)
    rw [← he, hcA]
  · exact h3


/-- Adding globally fixed vectors does not change a pointwise centralizer. -/
private theorem kernel_sup_global_fixed (ρ : Representation (ZMod 2) G V)
    (W : Submodule (ZMod 2) V) :
    subspaceKernel ρ (W ⊔ fixedSpace ρ ⊤) ⊤ = subspaceKernel ρ W ⊤ := by
  ext g
  constructor
  · intro hg
    exact ⟨mem_top g,fun w hw => hg.2 w (Submodule.mem_sup_left hw)⟩
  · intro hg
    refine ⟨mem_top g, ?_⟩
    intro v hv
    obtain ⟨w,hw,u,hu,rfl⟩ := Submodule.mem_sup.mp hv
    have hu' : ρ g u = u := hu ⟨g,mem_top g⟩
    rw [map_add, hg.2 w hw, hu']

/-- The centralizer of a subgroup's fixed space is normalized by that
subgroup's normalizer. This retains the literal module centralizer. -/
private theorem normalizer_le_kernel_normalizer (ρ : Representation (ZMod 2) G V)
    (Z : Subgroup G) :
    normalizer (Z : Set G) ≤
      normalizer (subspaceKernel ρ (fixedSpace ρ Z) ⊤ : Set G) := by
  let A := subspaceKernel ρ (fixedSpace ρ Z) ⊤
  have hstable (g : G) (hg : g ∈ normalizer (Z : Set G))
      (v : V) (hv : v ∈ fixedSpace ρ Z) : ρ g v ∈ fixedSpace ρ Z := by
    intro z
    have hz : g⁻¹ * z * g ∈ Z := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp
        ((normalizer (Z : Set G)).inv_mem hg) z).mp z.property
    have hv' : ρ (g⁻¹ * z * g) v = v := hv ⟨_,hz⟩
    change ρ z (ρ g v) = ρ g v
    calc
      _ = ρ g (ρ (g⁻¹ * z * g) v) := by
        simp only [map_mul, Module.End.mul_apply]
        simp
      _ = _ := congrArg (ρ g) hv'
  have hconj (g : G) (hg : g ∈ normalizer (Z : Set G))
      (a : G) (ha : a ∈ A) : g * a * g⁻¹ ∈ A := by
    refine ⟨mem_top _, ?_⟩
    intro v hv
    have hi := hstable g⁻¹ ((normalizer (Z : Set G)).inv_mem hg) v hv
    rw [map_mul, map_mul]
    simp only [Module.End.mul_apply, ha.2 _ hi]
    simp
  intro g hg
  apply mem_normalizer_iff.mpr
  intro a
  constructor
  · exact hconj g hg a
  · intro ha
    have hi := hconj g⁻¹ ((normalizer (Z : Set G)).inv_mem hg) _ ha
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hi


open Representation.BinaryOffender

/-- The literal family of ambient conjugates of A contained in R. -/
def conjugatesIn (A R : Subgroup G) : Set (Subgroup G) :=
  {B | (∃ g : G, conjugate A g = B) ∧ B ≤ R}

/-- Earlier B.4.6 inputs, with its own numbering: Z₁ is the center of the
point radical, Z₂ the long-root center of the line radical P.pCoreIn 2.
The root-fusion input concerns order-two long-root groups, not offenders.
`offenders` and `thompson` use the genuine B.1 definitions. No orbit size
or transitivity on offenders is a field of this structure. -/
structure B46Premises (ρ : Representation (ZMod 2) G V)
    (W : Submodule (ZMod 2) V) (P : Subgroup G) where
  Z₁ : Subgroup G
  Z₂ : Subgroup G
  T : Sylow 2 G
  long_root_le : Z₂ ≤ Z₁
  strong_closed : Theory.GroupTheory.IsStronglyClosedSet (Z₁ : Set G)
    (centralizer (Z₁ : Set G)) ⊤
  root_fusion : ∀ g : G, conjugate Z₂ g ≤ Z₁ →
    ∃ n ∈ normalizer (Z₁ : Set G), conjugate Z₂ n = conjugate Z₂ g
  line_normalizer : normalizer (Z₂ : Set G) = P
  radical_centralizes : P.pCoreIn 2 ≤ centralizer (Z₂ : Set G)
  borel_normalizes : (T : Subgroup G) ≤ normalizer (Z₁ : Set G)
  borel_index : (T : Subgroup G).relIndex P = 3
  root_plane_fixed : fixedSpace ρ Z₁ = W ⊔ fixedSpace ρ ⊤
  offender_le_sylow : subspaceKernel ρ W ⊤ ≤ (T : Subgroup G)
  offenders : ∀ B, IsBestOffender ρ B ↔
    ∃ g : G, conjugate (subspaceKernel ρ W ⊤) g = B
  thompson : generatedBy {B | IsBestOffender ρ B} (T : Subgroup G) = P.pCoreIn 2
  offender_card : Nat.card (subspaceKernel ρ W ⊤) = 8
  radical_card : Nat.card (P.pCoreIn 2) = 32

/-- B.4.6's root argument gives exactly three offender conjugates in its
R₂, all conjugate under its P₂. Chapter 14 calls these R₁* and M₁*. -/
theorem three_conjugates_of_B46 (ρ : Representation (ZMod 2) G V)
    (W : Submodule (ZMod 2) V) (P : Subgroup G) (d : B46Premises ρ W P) :
    let A := subspaceKernel ρ W ⊤
    conjugatesIn A (P.pCoreIn 2) = conjugateLineFamily A P ∧
      (conjugatesIn A (P.pCoreIn 2)).ncard = 3 := by
  dsimp only
  let A := subspaceKernel ρ W ⊤
  have hA : subspaceKernel ρ (fixedSpace ρ d.Z₁) ⊤ = A := by
    rw [d.root_plane_fixed, kernel_sup_global_fixed]
  have hZA : d.Z₁ ≤ A := by
    rw [← hA]
    intro z hz
    exact ⟨mem_top z, fun v hv => hv ⟨z,hz⟩⟩
  have hAN : normalizer (d.Z₁ : Set G) ≤ normalizer (A : Set G) := by
    rw [← hA]
    exact normalizer_le_kernel_normalizer ρ d.Z₁
  have hAR : A ≤ P.pCoreIn 2 := by
    rw [← d.thompson]
    exact le_iSup_of_le A (le_iSup_of_le
      ⟨(d.offenders A).mpr ⟨1,conj_one A⟩,d.offender_le_sylow⟩ le_rfl)
  have hfusion (g : G) (hg : conjugate A g ≤ P.pCoreIn 2) :
      ∃ c ∈ P, conjugate A c = conjugate A g := by
    rw [← d.line_normalizer]
    exact offender_fusion d.Z₁ d.Z₂ A _ hZA d.long_root_le
      d.strong_closed d.radical_centralizes hAN d.root_fusion g hg
  have hPN : P ≤ normalizer (P.pCoreIn 2 : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have he : conjugatesIn A (P.pCoreIn 2) = conjugateLineFamily A P := by
    ext B
    constructor
    · rintro ⟨⟨g,rfl⟩,hg⟩
      obtain ⟨c,hc,he⟩ := hfusion g hg
      exact ⟨⟨c,hc⟩,he⟩
    · rintro ⟨c,rfl⟩
      refine ⟨⟨c,rfl⟩,?_⟩
      have hc : conjugate (P.pCoreIn 2) c = P.pCoreIn 2 :=
        mem_normalizer_iff_map_conj_eq.mp (hPN c.property)
      rw [← hc]
      exact map_mono hAR
  refine ⟨he,?_⟩
  rw [he]
  apply count_from_generation ρ A (d.T : Subgroup G) P (P.pCoreIn 2) hAR
    (d.borel_normalizes.trans hAN) d.borel_index d.offenders d.thompson _ hfusion
  intro heq
  have hcard := congrArg (fun B : Subgroup G => Nat.card B) heq
  rw [d.offender_card, d.radical_card] at hcard
  omega

/-- The two actual representations supplied by 14.7.54. -/
inductive BinaryG2Module
  | natural
  | weyl

open Atlas.G2 Atlas.G2.Natural
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon

/-- The actual six-dimensional scalar quotient or seven-dimensional trace-zero space. -/
def BinaryG2Module.Space : BinaryG2Module → Type
  | .natural => Atlas.G2.Natural.Space (ZMod 2)
  | .weyl => TraceZero (ZMod 2)

instance instAddCommGroupSpace (m : BinaryG2Module) : AddCommGroup m.Space :=
  match m with
  | .natural => inferInstanceAs (AddCommGroup (Atlas.G2.Natural.Space (ZMod 2)))
  | .weyl => inferInstanceAs (AddCommGroup (TraceZero (ZMod 2)))
instance instModuleSpace (m : BinaryG2Module) : Module (ZMod 2) m.Space :=
  match m with
  | .natural => inferInstanceAs (Module (ZMod 2) (Atlas.G2.Natural.Space (ZMod 2)))
  | .weyl => inferInstanceAs (Module (ZMod 2) (TraceZero (ZMod 2)))

/-- The marked action of the full octonion automorphism group G₂(2). -/
def BinaryG2Module.action (m : BinaryG2Module) :
    Representation (ZMod 2) (Model (ZMod 2)) m.Space :=
  match m with
  | .natural => Atlas.G2.Natural.action (ZMod 2)
  | .weyl => traceZeroAction (ZMod 2)

/-- The existing singular-subspace realization in the same representation. -/
def BinaryG2Module.singularMap (m : BinaryG2Module) : SingularMap m.Space :=
  match m with
  | .natural => naturalMap
  | .weyl => weylMap

/-- The pencil used below is equivariant for the full marked action. -/
theorem BinaryG2Module.equivariant (m : BinaryG2Module) :
    m.singularMap.Equivariant m.action := by
  cases m
  · exact naturalMap_equivariant
  · exact weylMap_equivariant

/-- The literal span Ũ(V₁,V₂) of the doubly singular lines through the marked point. -/
def BinaryG2Module.pencilSpan (m : BinaryG2Module) (p : SingularPoints (ZMod 2)) :
    Submodule (ZMod 2) m.Space :=
  ⨆ L : {L : ZeroProductLine (ZMod 2) // pointOnLine p L}, m.singularMap.line L.val

variable {H : Type*} [Group H]

/-- H* is identified with the full G₂(2), and A* is the pointwise centralizer
of the marked pencil span in its actual natural/Weyl action. -/
def markedOffender (m : BinaryG2Module)
    (e : (H ⧸ pCore 2 H) ≃* Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    Subgroup (H ⧸ pCore 2 H) :=
  subspaceKernel (m.action.comp e.toMonoidHom) (m.pencilSpan p) ⊤

/-- The marked application of B.4.6 proving 14.7.57(3). The actual image of
M₁ is the stabilizer of the marked line, as supplied by `ParabolicLift`.
The radical in the conclusion is literally the image of O₂(M₁) under
H → H/O₂(H). All extra premises are earlier B.4.6 facts, whose source
producer is `qt-b-04-g2`; the parent owns their final discharge. -/
theorem source_three_offender_conjugates [Finite H] (m : BinaryG2Module)
    (e : (H ⧸ pCore 2 H) ≃* Model (ZMod 2))
    (p : SingularPoints (ZMod 2)) (L : ZeroProductLine (ZMod 2))
    (M₁ : Subgroup H)
    (hM : M₁.map (QuotientGroup.mk' (pCore 2 H)) =
      (MulAction.stabilizer (Model (ZMod 2)) L).comap e.toMonoidHom)
    (d : B46Premises (m.action.comp e.toMonoidHom) (m.pencilSpan p)
      ((MulAction.stabilizer (Model (ZMod 2)) L).comap e.toMonoidHom)) :
    let π := QuotientGroup.mk' (pCore 2 H)
    let A := markedOffender m e p
    let R := (M₁.pCoreIn 2).map π
    conjugatesIn A R = conjugateLineFamily A (M₁.map π) ∧
      (conjugatesIn A R).ncard = 3 ∧
      ∀ B ∈ conjugatesIn A R, ∃ x : M₁, conjugate A (π x) = B := by
  dsimp only
  let π := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hR : (M₁.pCoreIn 2).map π = (M₁.map π).pCoreIn 2 :=
    map_pCoreIn_of_ker_isPGroup π hk M₁
  have h := three_conjugates_of_B46 (m.action.comp e.toMonoidHom) (m.pencilSpan p) _ d
  change conjugatesIn (markedOffender m e p) _ = _ ∧ _ at h
  rw [← hM] at h
  rw [← hR] at h
  refine ⟨h.1,h.2,?_⟩
  intro B hB
  rw [h.1] at hB
  obtain ⟨c,hc⟩ := hB
  obtain ⟨x,hx,he⟩ := c.property
  refine ⟨⟨x,hx⟩,?_⟩
  change conjugate (markedOffender m e p) (π x) = B
  rw [he]
  exact hc

/-- Identify the actual source centralizer through the equivariant module
isomorphism, including the specified three-space rather than just its dimension. -/
theorem source_centralizer_eq_marked (m : BinaryG2Module)
    (e : (H ⧸ pCore 2 H) ≃* Model (ZMod 2)) (p : SingularPoints (ZMod 2))
    (ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) V)
    (E : V ≃ₗ[ZMod 2] m.Space)
    (hE : ∀ g v, E (ρ g v) = m.action (e g) (E v))
    (U₃ : Submodule (ZMod 2) V) (hU : U₃.map E.toLinearMap = m.pencilSpan p) :
    subspaceKernel ρ U₃ ⊤ = markedOffender m e p := by
  ext g
  constructor
  · intro hg
    refine ⟨mem_top g,?_⟩
    intro v hv
    rw [← hU] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    change m.action (e g) (E w) = E w
    rw [← hE, hg.2 w hw]
  · intro hg
    refine ⟨mem_top g,?_⟩
    intro v hv
    apply E.injective
    rw [hE]
    apply hg.2
    rw [← hU]
    exact Submodule.mem_map_of_mem hv

/-- Source 14.7.57(3) on the original marked module: A*=C_{H*}(Ũ(V₁,V₂)),
R₁*=O₂(M₁)*, and each of the three conjugates is reached by an actual
member of M₁ acting through the literal quotient map. The earlier B.4.6
premises remain explicit for their existing source producer. -/
theorem source_three_offender_conjugates_on_module [Finite H] (m : BinaryG2Module)
    (e : (H ⧸ pCore 2 H) ≃* Model (ZMod 2))
    (p : SingularPoints (ZMod 2)) (L : ZeroProductLine (ZMod 2))
    (ρ : Representation (ZMod 2) (H ⧸ pCore 2 H) V)
    (E : V ≃ₗ[ZMod 2] m.Space)
    (hE : ∀ g v, E (ρ g v) = m.action (e g) (E v))
    (U₃ : Submodule (ZMod 2) V) (hU : U₃.map E.toLinearMap = m.pencilSpan p)
    (M₁ : Subgroup H)
    (hM : M₁.map (QuotientGroup.mk' (pCore 2 H)) =
      (MulAction.stabilizer (Model (ZMod 2)) L).comap e.toMonoidHom)
    (d : B46Premises (m.action.comp e.toMonoidHom) (m.pencilSpan p)
      ((MulAction.stabilizer (Model (ZMod 2)) L).comap e.toMonoidHom)) :
    let π := QuotientGroup.mk' (pCore 2 H)
    let A := subspaceKernel ρ U₃ ⊤
    let R := (M₁.pCoreIn 2).map π
    conjugatesIn A R = conjugateLineFamily A (M₁.map π) ∧
      (conjugatesIn A R).ncard = 3 ∧
      ∀ B ∈ conjugatesIn A R, ∃ x : M₁, conjugate A (π x) = B := by
  dsimp only
  rw [source_centralizer_eq_marked m e p ρ E hE U₃ hU]
  exact source_three_offender_conjugates m e p L M₁ hM d

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.LocalParabolics.ThreeOffenderOrbit
