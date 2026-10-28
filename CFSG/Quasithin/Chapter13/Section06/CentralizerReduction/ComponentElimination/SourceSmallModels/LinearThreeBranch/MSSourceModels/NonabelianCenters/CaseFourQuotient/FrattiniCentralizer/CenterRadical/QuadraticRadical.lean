module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.QuadraticRadical.FixedQuotient

/-!
# The conditional center equality in C.1.34(4)

Let Q be the genuine MS core, P = Φ(Q), Z = Z(Q), U = [Z,K], and D = C_Q(P).
Assume P is elementary, squares of D lie in Z, and D is nonabelian.
Squares modulo U are additive and invariant, hence vanish on D/P, a doubled
dual natural module. The resulting square map D/P → U vanishes on each pure
factor. The actual commutator pairing is therefore nonzero with zero radical,
which proves Z(D) = P. All sections use the one given quotient marking e.

The final quotient application retains these three assumptions and the
independently owned FrattiniCommutatorLarge premise. The parent assembly must
discharge the two structural assumptions; this is a conditional algebraic
consequence of C.1.34(4), not a new assertion that the book displays the equality.

Source: Aschbacher–Smith C.1.34(4), printed pp.136–137; MS93 Lemma 4.5,
printed pp.895–900, with the binary square/radical calculation from (4.6).
-/

public section
open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.QuadraticRadical

local notation "sCenter" => CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.centerIn
variable {G : Type*} [Group G] {K R S : Subgroup G} {κ : CFSG.Quasithin.GroupClass}

private theorem natural_coordinates {U : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (h : HasSectionModel K U ⊥ (linearThreeActor e) BinaryLinearThree.W) :
    ∃ u : U ≃* Multiplicative BinaryLinearThree.Vector,
      ∀ (k : K) (x y : U), (y:G) = k*(x:G)*(k:G)⁻¹ →
        (u y).toAdd = BinaryLinearThree.W (linearThreeActor e k) (u x).toAdd := by
  obtain ⟨_,_,_,hn,f,hf⟩ := h
  let := hn
  have hi : Function.Injective (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf U)) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk', bot_subgroupOf]
  let j := f.toMonoidHom.comp (QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf U))
  let u := MulEquiv.ofBijective j ⟨f.injective.comp hi,
    f.surjective.comp (QuotientGroup.mk'_surjective _)⟩
  exact ⟨u,hf⟩

variable [Finite G]

/-- The doubled-dual radical calculation for the genuine fourth alternative,
with elementarity and square placement still explicit. -/
theorem caseFour_center_centralizer_le_frattini
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hP : IsElementaryAbelian 2 (frattiniIn (msQ K R)))
    (hsq : ∀ x ∈ msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      x^2 ∈ sCenter (msQ K R))
    (hne : ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)⁆ ≠ ⊥) :
    sCenter (msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)) ≤
      frattiniIn (msQ K R) := by
  let Q := msQ K R
  let Z := sCenter Q
  let P := frattiniIn Q
  let D := Q ⊓ centralizer (P : Set G)
  let U := ⁅Z,K⁆
  have hZP : Z ≤ P := h.2.2.2.2.2.2.1.1
  have hmodel := h.2.2.2.2.2.2.2.1
  have hPD : P ≤ D := hmodel.1
  have hUZ : U ≤ Z :=
    le_sup_right.trans_eq h.2.2.2.1.symm
  have hUD : U ≤ D := hUZ.trans (hZP.trans hPD)
  have hZcQ : Z ≤ centralizer (Q : Set G) := (centerIn_eq Q).le.trans inf_le_right
  have hZcD : Z ≤ centralizer (D : Set G) := hZcQ.trans (centralizer_le inf_le_left)
  have hPc : P ≤ sCenter D := caseFour_frattini_le_center_centralizer e h
  have hDD : ⁅D,D⁆ ≤ U := caseFour_centralizer_derived_le_moved_center hMS e h
  obtain ⟨q,hq,hker,hqact⟩ := section_coordinates (linearThreeActor e) hmodel
  have hZZ : IsMulCommutative Z := (caseFour_center_elementary e h).toIsMulCommutative
  have hsqU : ∀ x ∈ D, x^2 ∈ U := squares_mem_moved
    (linearThreeActor e) (linearThreeActor_surjective e)
    q hq hker hqact hmodel.2.1 hZcD hZZ hUZ le_rfl hDD hP hsq
  obtain ⟨u,hu⟩ := natural_coordinates e h.2.2.2.2.2.1
  let a : K →* MulAut D := D.normalizerMonoidHom.comp (inclusion hmodel.2.1)
  have hkc : q.ker ≤ center D := by
    intro x hx
    have hxP : (x:G) ∈ P := by
      change x ∈ P.subgroupOf D
      rwa [← hker]
    have hh := (centerIn_eq D).le (hPc hxP)
    exact mem_center_iff.mpr (fun y => Subtype.ext (hh.2 y y.property))
  let d : Extension D K := {
    actor := linearThreeActor e
    actor_surjective := linearThreeActor_surjective e
    action := a
    quotient := q
    onto := hq
    kernel_central := hkc
    kernel_square := by
      intro x
      have hxP : ((x:D):G) ∈ P := by
        change (x:D) ∈ P.subgroupOf D
        rw [← hker]
        exact x.property
      let := hP
      apply Subtype.ext
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p:=2) _ hxP
    U := U.subgroupOf D
    coordinates := (subgroupOfEquivOfLe hUD).trans u
    square_mem := fun x => hsqU x x.property
    commutator_mem := fun x y => hDD (commutator_mem_commutator x.property y.property)
    quotient_action := fun k x => hqact k x (a k x) rfl
    coordinates_action := by
      intro k x y hy
      apply hu k (subgroupOfEquivOfLe hUD x) (subgroupOfEquivOfLe hUD y)
      exact congrArg Subtype.val hy }
  have hnon : ∃ x y : D, ⁅x,y⁆ ≠ 1 := by
    by_contra! hh
    apply hne
    apply le_bot_iff.mp
    apply commutator_le.mpr
    intro x hx y hy
    exact (mem_bot).mpr (congrArg Subtype.val (hh ⟨x,hx⟩ ⟨y,hy⟩))
  have hc := d.center_le_kernel hnon
  rintro x ⟨y,hy,rfl⟩
  change y ∈ P.subgroupOf D
  rw [← hker]
  exact hc hy

/-- The already central Frattini subgroup is the entire center. -/
theorem caseFour_center_centralizer_eq_frattini
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hP : IsElementaryAbelian 2 (frattiniIn (msQ K R)))
    (hsq : ∀ x ∈ msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      x^2 ∈ sCenter (msQ K R))
    (hne : ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)⁆ ≠ ⊥) :
    sCenter (msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)) =
      frattiniIn (msQ K R) :=
  le_antisymm (caseFour_center_centralizer_le_frattini hMS e h hP hsq hne)
    (caseFour_frattini_le_center_centralizer e h)

/-- Conditional application to the literal quotient consumer, retaining the
separately owned large-Frattini-commutator premise. -/
theorem caseFour_quotient_control_of_quadratic {H : Type*} [Group H]
    (hMS : LinearThreeMSPair κ K R 1 (ZMod 2))
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) (h : CaseFour K R S e)
    (hP : IsElementaryAbelian 2 (frattiniIn (msQ K R)))
    (hsq : ∀ x ∈ msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      x^2 ∈ sCenter (msQ K R))
    (hne : ⁅msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G),
      msQ K R ⊓ centralizer (frattiniIn (msQ K R) : Set G)⁆ ≠ ⊥)
    (f : K →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcard : Nat.card f.ker ∣ 2)
    (hN : f.ker.map K.subtype ≤ sCenter (K ⊔ R))
    (hPhi : FrattiniCommutatorLarge (msQ K R)) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ ≤ sCenter (pCore 2 K) ∧
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup K)⁆ =
      ⁅sCenter (pCore 2 K), (⊤ : Subgroup K)⁆ :=
  caseFour_quotient_control_of_center hMS e h f hf hk hcard hN
    (caseFour_center_centralizer_le_frattini hMS e h hP hsq hne) hPhi

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.QuadraticRadical
