module

import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.Algebra.Group.Commutator
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Multiplicity
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Commutator.Finite
public import Mathlib.GroupTheory.CommutingProbability
public import Mathlib.GroupTheory.Complement
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfFixingSubgroup
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.Perm.Closure
import Mathlib.GroupTheory.Perm.Cycle.Factors
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Schreier
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Transfer
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NoncommRing
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

public import Theory.Alternating.proposition_5_2_4
set_option linter.style.nameCheck false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000

/- Chapter 5-specific declarations, kept out of the general Theory library. -/

/- BEGIN Theory.RootSubextension -/
set_option maxHeartbeats 800000

noncomputable section

open Theory.GroupTheory
open Theory.GroupTheory.Covering

namespace GLS3.Chapter5.Covering
universe __ch5_RootSubextension_u __ch5_RootSubextension_v __ch5_RootSubextension_w

/-- Divisibility strengthening of the universal covering-kernel bound: every
covering kernel is a quotient of the universal kernel. -/
public theorem coveringKernel_card_dvd_of_universal
    {L₀ : Type __ch5_RootSubextension_u} {G : Type __ch5_RootSubextension_v} {M : Type __ch5_RootSubextension_w}
    [Group L₀] [Finite L₀] [IsQuasisimple L₀]
    [Group G] [Finite G] [IsQuasisimple G]
    [Group M] [Finite M] [IsQuasisimple M]
    (f₀ : Covering L₀ G) (hf₀ : IsUniversal.{__ch5_RootSubextension_v, __ch5_RootSubextension_u, __ch5_RootSubextension_w} f₀)
    (g : Covering M G) :
    Nat.card g.toMonoidHom.ker ∣ Nat.card f₀.toMonoidHom.ker := by
  let h := IsUniversal.lift hf₀ g
  let φ : f₀.toMonoidHom.ker →* g.toMonoidHom.ker :=
    (h.toMonoidHom.comp f₀.toMonoidHom.ker.subtype).codRestrict
      g.toMonoidHom.ker (by
        intro x
        rw [MonoidHom.mem_ker]
        change g (h x.1) = 1
        have hfac (z : L₀) : g (h z) = f₀ z := by
          simpa [h] using DFunLike.congr_fun (IsUniversal.lift_fac hf₀ g) z
        rw [hfac]
        exact MonoidHom.mem_ker.mp x.2)
  have hφ : Function.Surjective φ := by
    intro y
    have hy : y.1 ∈ Subgroup.map h.toMonoidHom f₀.toMonoidHom.ker := by
      rw [coveringKernel_image_of_universal f₀ hf₀ g]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  exact Subgroup.card_dvd_of_surjective φ hφ

end GLS3.Chapter5.Covering

namespace GLS3.Chapter5.SchurPresentation

open RootAm

/-! ## A1 33.18: restriction to a root `A₅`

For a finite central extension of `A_{n+5}`, restrict to the full preimage of
the standard root `A₅` and then pass to its derived subgroup.  The resulting
covering of `A₅` has kernel of order at most two by A1 33.17.  This is the
local input used to eliminate odd primary parts of alternating multipliers.
-/

/-! ### General root `A_m` restriction -/

/-- The standard root `A_m` is canonically isomorphic to the alternating
group on its source points. -/
@[expose] public noncomputable def centralRootAmEquiv
    (n m : Nat) (hmn : m ≤ n + 5) :
    alternatingGroup (Fin ((m - 5) + 5)) ≃* rootAm n m hmn := by
  apply MulEquiv.ofBijective (tailAltHom n m hmn).rangeRestrict
  exact ⟨fun _ _ h => tailAltHom_injective n m hmn
    (congrArg Subtype.val h), (tailAltHom n m hmn).rangeRestrict_surjective⟩

/-- The full preimage of a standard root `A_m` in a central extension. -/
public abbrev centralRootAmPreimage
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5))) : Subgroup H :=
  (rootAm n m hmn).comap f

/-- Projection from the full root `A_m` preimage to the abstract `A_m`. -/
@[expose]
public noncomputable def centralRootAmPreimageProjection
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5))) :
    centralRootAmPreimage n m hmn f →*
      alternatingGroup (Fin ((m - 5) + 5)) :=
  (centralRootAmEquiv n m hmn).symm.toMonoidHom.comp
    ((f.comp (centralRootAmPreimage n m hmn f).subtype).codRestrict
      (rootAm n m hmn) (fun x => x.2))

/-- The root `A_m` preimage projection is surjective. -/
public theorem centralRootAmPreimageProjection_surjective
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f) :
    Function.Surjective (centralRootAmPreimageProjection n m hmn f) := by
  intro y
  let y' : rootAm n m hmn := centralRootAmEquiv n m hmn y
  obtain ⟨x, hx⟩ := hsurj y'.1
  have hxRoot : f x ∈ rootAm n m hmn := hx.symm ▸ y'.2
  refine ⟨⟨x, hxRoot⟩, ?_⟩
  change (centralRootAmEquiv n m hmn).symm ⟨f x, hxRoot⟩ = y
  apply (centralRootAmEquiv n m hmn).injective
  rw [(centralRootAmEquiv n m hmn).apply_symm_apply]
  apply Subtype.ext
  exact hx

/-- A central extension restricts to a central extension of a root `A_m`. -/
public theorem centralRootAmPreimageProjection_ker_le_center
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hker : f.ker ≤ Subgroup.center H) :
    (centralRootAmPreimageProjection n m hmn f).ker ≤
      Subgroup.center (centralRootAmPreimage n m hmn f) := by
  let r0 : centralRootAmPreimage n m hmn f →* rootAm n m hmn :=
    (f.comp (centralRootAmPreimage n m hmn f).subtype).codRestrict
      (rootAm n m hmn) (fun x => x.2)
  have hkerEq : (centralRootAmPreimageProjection n m hmn f).ker = r0.ker :=
    MonoidHom.ker_comp_of_injective r0
      (centralRootAmEquiv n m hmn).symm.toMonoidHom
      (centralRootAmEquiv n m hmn).symm.injective
  intro x hx
  have hx0 : x ∈ r0.ker := by rwa [← hkerEq]
  have hxGlobal : (x : H) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx0)
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hxGlobal) y.1

/-- The root `A_m` projection kernel is the restriction of the global
extension kernel. -/
public theorem centralRootAmPreimageProjection_ker_eq_comap
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5))) :
    (centralRootAmPreimageProjection n m hmn f).ker =
      f.ker.comap (centralRootAmPreimage n m hmn f).subtype := by
  let r0 : centralRootAmPreimage n m hmn f →* rootAm n m hmn :=
    (f.comp (centralRootAmPreimage n m hmn f).subtype).codRestrict
      (rootAm n m hmn) (fun x => x.2)
  calc
    (centralRootAmPreimageProjection n m hmn f).ker = r0.ker :=
      MonoidHom.ker_comp_of_injective r0
        (centralRootAmEquiv n m hmn).symm.toMonoidHom
        (centralRootAmEquiv n m hmn).symm.injective
    _ = f.ker.comap (centralRootAmPreimage n m hmn f).subtype := by
      ext x
      dsimp [r0]
      constructor
      · intro hx
        have hx0 := MonoidHom.mem_ker.mp hx
        have hfx : f x = 1 := congrArg Subtype.val hx0
        exact MonoidHom.mem_ker.mpr hfx
      · intro hx
        have hx' : (x : H) ∈ f.ker := hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hx'

/-- The derived subgroup of the full root `A_m` preimage. -/
public abbrev centralRootAmPreimageDerived
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5))) :=
  commutator (centralRootAmPreimage n m hmn f)

/-- The root `A_m` projection restricted to the derived subgroup of its full
preimage. -/
@[expose]
public noncomputable def centralRootAmPreimageDerivedProjection
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5))) :
    centralRootAmPreimageDerived n m hmn f →*
      alternatingGroup (Fin ((m - 5) + 5)) :=
  (centralRootAmPreimageProjection n m hmn f).comp
    (centralRootAmPreimageDerived n m hmn f).subtype

/-- The derived restriction kernel is the corresponding intersection with
the root-preimage kernel. -/
public theorem centralRootAmPreimageDerivedProjection_ker_eq_comap
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5))) :
    (centralRootAmPreimageDerivedProjection n m hmn f).ker =
      (centralRootAmPreimageProjection n m hmn f).ker.comap
        (centralRootAmPreimageDerived n m hmn f).subtype := by
  rfl

/-- The derived root `A_m` preimage still maps onto `A_m`. -/
public theorem centralRootAmPreimageDerivedProjection_surjective
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f) :
    Function.Surjective
      (centralRootAmPreimageDerivedProjection n m hmn f) := by
  let E := centralRootAmPreimage n m hmn f
  let r := centralRootAmPreimageProjection n m hmn f
  have hrRange : r.range = ⊤ :=
    MonoidHom.range_eq_top.mpr
      (centralRootAmPreimageProjection_surjective n m hmn f hsurj)
  have hmap : (commutator E).map r = ⊤ := by
    rw [map_commutator_eq, hrRange]
    exact Group.IsPerfect.commutator_eq_top
  intro y
  have hy : y ∈ (commutator E).map r := by rw [hmap]; trivial
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, hxy⟩

/-- The derived root `A_m` preimage is again a central extension. -/
public theorem centralRootAmPreimageDerivedProjection_ker_le_center
    {H : Type*} [Group H] (n m : Nat) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hker : f.ker ≤ Subgroup.center H) :
    (centralRootAmPreimageDerivedProjection n m hmn f).ker ≤
      Subgroup.center (centralRootAmPreimageDerived n m hmn f) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx' : (x : centralRootAmPreimage n m hmn f) ∈
      (centralRootAmPreimageProjection n m hmn f).ker := hx
  exact Subgroup.mem_center_iff.mp
    (centralRootAmPreimageProjection_ker_le_center n m hmn f hker hx') y

/-- General root-restriction divisibility used in A1 33.20--33.22: the kernel
of the derived root `A_m` covering is a quotient of the Schur multiplier of
`A_m`. -/
public theorem centralRootAmPreimageDerivedProjection_ker_card_dvd_multiplier
    {H : Type*} [Group H] [Finite H]
    (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Nat.card (centralRootAmPreimageDerivedProjection n m hmn f).ker ∣
      Nat.card (alternatingFreeCentralCovering (m - 5)).toMonoidHom.ker := by
  let D := centralRootAmPreimageDerived n m hmn f
  let r := centralRootAmPreimageProjection n m hmn f
  let rD := centralRootAmPreimageDerivedProjection n m hmn f
  let : Group.IsPerfect D :=
    commutator_isPerfect_of_surjective_of_ker_le_center r
      (centralRootAmPreimageProjection_surjective n m hmn f hsurj)
      (centralRootAmPreimageProjection_ker_le_center n m hmn f hker)
  let : Finite D := inferInstance
  have hrDsurj : Function.Surjective rD :=
    centralRootAmPreimageDerivedProjection_surjective n m hmn f hsurj
  have hrDcenter : rD.ker ≤ Subgroup.center D :=
    centralRootAmPreimageDerivedProjection_ker_le_center n m hmn f hker
  have hrDker : rD.ker = Subgroup.center D := by
    apply ker_eq_center_of_surjective_of_center_eq_bot rD hrDsurj hrDcenter
    exact alternatingGroup.center_eq_bot (by
      simpa only [Nat.card_fin, Nat.sub_add_cancel h5] using (show 4 ≤ m by omega))
  let e : D ⧸ Subgroup.center D ≃*
      alternatingGroup (Fin ((m - 5) + 5)) :=
    (QuotientGroup.quotientMulEquivOfEq hrDker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective rD hrDsurj)
  let : IsQuasisimple D := {
    toIsPerfect := inferInstance
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin ((m - 5) + 5))) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
  }
  let c : Covering D (alternatingGroup (Fin ((m - 5) + 5))) := {
    toMonoidHom := rD
    surjective := hrDsurj
  }
  exact Covering.coveringKernel_card_dvd_of_universal
    (alternatingFreeCentralCovering (m - 5))
    (alternatingFreeCentralCovering_isUniversal (m - 5)) c

/-- Cardinality-bound form of the general root-restriction theorem. -/
public theorem centralRootAmPreimageDerivedProjection_ker_card_le_multiplier
    {H : Type*} [Group H] [Finite H]
    (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Nat.card (centralRootAmPreimageDerivedProjection n m hmn f).ker ≤
      Nat.card (alternatingFreeCentralCovering (m - 5)).toMonoidHom.ker :=
  Nat.le_of_dvd Nat.card_pos
    (centralRootAmPreimageDerivedProjection_ker_card_dvd_multiplier
      n m h5 hmn f hsurj hker)

/-- If a prime supporting the global central kernel does not divide the
smaller alternating multiplier, then the derived root `A_m` restriction has
trivial kernel. -/
public theorem
    centralRootAmPreimageDerivedProjection_ker_eq_bot_of_not_dvd_multiplier
    {H : Type*} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering (m - 5)).toMonoidHom.ker) :
    (centralRootAmPreimageDerivedProjection n m hmn f).ker = ⊥ := by
  let rD := centralRootAmPreimageDerivedProjection n m hmn f
  have hkerpE : IsPGroup p
      (f.ker.comap (centralRootAmPreimage n m hmn f).subtype) :=
    hkerp.comap_subtype
  have hkerpD : IsPGroup p rD.ker := by
    rw [centralRootAmPreimageDerivedProjection_ker_eq_comap,
      centralRootAmPreimageProjection_ker_eq_comap]
    exact hkerpE.comap_subtype
  have hdvd : Nat.card rD.ker ∣ Nat.card
      (alternatingFreeCentralCovering (m - 5)).toMonoidHom.ker :=
    centralRootAmPreimageDerivedProjection_ker_card_dvd_multiplier
      n m h5 hmn f hsurj hker
  have hcard : Nat.card rD.ker = 1 := by
    rcases hkerpD.card_eq_or_dvd with h1 | hp
    · exact h1
    · exact False.elim (hpM (hp.trans hdvd))
  exact Subgroup.card_eq_one.mp hcard

/-- If the smaller alternating multiplier has no `p`-part, the global kernel
and the derived root `A_m` subgroup are complementary in the full root
preimage. -/
public theorem
    centralRootAmPreimageProjection_ker_isComplement'_derived_of_not_dvd_multiplier
    {H : Type*} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering (m - 5)).toMonoidHom.ker) :
    (centralRootAmPreimageProjection n m hmn f).ker.IsComplement'
      (centralRootAmPreimageDerived n m hmn f) := by
  let E := centralRootAmPreimage n m hmn f
  let r := centralRootAmPreimageProjection n m hmn f
  let D := centralRootAmPreimageDerived n m hmn f
  let rD := centralRootAmPreimageDerivedProjection n m hmn f
  have hkerD : rD.ker = ⊥ :=
    centralRootAmPreimageDerivedProjection_ker_eq_bot_of_not_dvd_multiplier
      n m h5 hmn f hsurj hker hkerp hpM
  have hdisj : Disjoint r.ker D := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxD
    let d : D := ⟨x, hxD⟩
    have hdker : d ∈ rD.ker := by
      rw [MonoidHom.mem_ker]
      exact MonoidHom.mem_ker.mp hxK
    have hd1 : d = 1 := by
      rw [hkerD] at hdker
      exact Subgroup.mem_bot.mp hdker
    exact congrArg Subtype.val hd1
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨d, hd⟩ :=
    centralRootAmPreimageDerivedProjection_surjective n m hmn f hsurj (r x)
  apply Set.mem_mul.mpr
  refine ⟨x * (d : E)⁻¹, ?_, d, d.2, ?_⟩
  · change x * (d : E)⁻¹ ∈ r.ker
    have hd' : r (d : E) = r x := hd
    rw [MonoidHom.mem_ker, map_mul, map_inv, hd']
    simp
  · simp

/-- Explicit direct-product form of the preceding inductive root splitting. -/
public noncomputable def centralRootAmPreimageKernelProdDerivedMulEquiv
    {H : Type*} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (n m : Nat) (h5 : 5 ≤ m) (hmn : m ≤ n + 5)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering (m - 5)).toMonoidHom.ker) :
    (centralRootAmPreimageProjection n m hmn f).ker ×
        centralRootAmPreimageDerived n m hmn f ≃*
      centralRootAmPreimage n m hmn f := by
  let E := centralRootAmPreimage n m hmn f
  let K := (centralRootAmPreimageProjection n m hmn f).ker
  let D := centralRootAmPreimageDerived n m hmn f
  let mHom : K × D →* E := {
    toFun := fun x => (x.1 : E) * (x.2 : E)
    map_one' := by simp
    map_mul' := by
      intro a b
      have hb1 : (b.1 : E) ∈ Subgroup.center E :=
        centralRootAmPreimageProjection_ker_le_center n m hmn f hker b.1.2
      have hc : (a.2 : E) * (b.1 : E) = (b.1 : E) * (a.2 : E) :=
        Subgroup.mem_center_iff.mp hb1 (a.2 : E)
      change ((a.1 : E) * (b.1 : E)) * ((a.2 : E) * (b.2 : E)) =
        ((a.1 : E) * (a.2 : E)) * ((b.1 : E) * (b.2 : E))
      calc
        _ = (a.1 : E) * ((b.1 : E) * (a.2 : E)) * (b.2 : E) := by
          simp only [mul_assoc]
        _ = (a.1 : E) * ((a.2 : E) * (b.1 : E)) * (b.2 : E) := by
          rw [← hc]
        _ = _ := by simp only [mul_assoc]
  }
  apply MulEquiv.ofBijective mHom
  exact
    centralRootAmPreimageProjection_ker_isComplement'_derived_of_not_dvd_multiplier
      n m h5 hmn f hsurj hker hkerp hpM

/-- The standard root `A₅` on the final five points. -/
public abbrev rootA5 (n : Nat) : Subgroup (alternatingGroup (Fin (n + 5))) :=
  rootAm n 5 (by omega)

/-- The standard root `A₅` is canonically isomorphic to `A₅`. -/
@[expose] public noncomputable def rootA5Equiv (n : Nat) :
    alternatingGroup (Fin 5) ≃* rootA5 n := by
  let t := (tailAltHom n 5 (by omega)).rangeRestrict
  apply MulEquiv.ofBijective t
  constructor
  · intro a b hab
    apply tailAltHom_injective n 5 (by omega)
    exact congrArg Subtype.val hab
  · exact (tailAltHom n 5 (by omega)).rangeRestrict_surjective

/-- The full preimage of the standard root `A₅` in an extension. -/
public abbrev rootA5Preimage
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5))) : Subgroup H :=
  (rootA5 n).comap f

/-- Projection from the full root preimage to the abstract `A₅`. -/
@[expose] public noncomputable def rootA5PreimageProjection
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5))) :
    rootA5Preimage n f →* alternatingGroup (Fin 5) :=
  (rootA5Equiv n).symm.toMonoidHom.comp
    ((f.comp (rootA5Preimage n f).subtype).codRestrict
      (rootA5 n) (fun x => x.2))

/-- The projection from the full root preimage is surjective. -/
public theorem rootA5PreimageProjection_surjective
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f) :
    Function.Surjective (rootA5PreimageProjection n f) := by
  intro y
  let y' : rootA5 n := rootA5Equiv n y
  obtain ⟨x, hx⟩ := hsurj y'.1
  have hxRoot : f x ∈ rootA5 n := by
    exact hx.symm ▸ y'.2
  have hxL : x ∈ rootA5Preimage n f := hxRoot
  refine ⟨⟨x, hxL⟩, ?_⟩
  change (rootA5Equiv n).symm ⟨f x, hxRoot⟩ = y
  apply (rootA5Equiv n).injective
  rw [(rootA5Equiv n).apply_symm_apply]
  apply Subtype.ext
  exact hx

/-- A central extension restricts to a central extension of the root `A₅`. -/
public theorem rootA5PreimageProjection_ker_le_center
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hker : f.ker ≤ Subgroup.center H) :
    (rootA5PreimageProjection n f).ker ≤
      Subgroup.center (rootA5Preimage n f) := by
  let r0 : rootA5Preimage n f →* rootA5 n :=
    (f.comp (rootA5Preimage n f).subtype).codRestrict
      (rootA5 n) (fun x => x.2)
  have hkerEq : (rootA5PreimageProjection n f).ker = r0.ker := by
    exact MonoidHom.ker_comp_of_injective r0 (rootA5Equiv n).symm.toMonoidHom
      (rootA5Equiv n).symm.injective
  intro x hx
  have hx0 : x ∈ r0.ker := by rwa [← hkerEq]
  have hxGlobal : (x : H) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have hx0' := MonoidHom.mem_ker.mp hx0
    exact congrArg Subtype.val hx0'
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hxGlobal) y.1

/-- The derived subgroup of the full preimage of the root `A₅`. -/
public abbrev rootA5PreimageDerived
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5))) :=
  commutator (rootA5Preimage n f)

/-- The root-preimage projection restricted to its derived subgroup. -/
@[expose] public noncomputable def rootA5PreimageDerivedProjection
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5))) :
    rootA5PreimageDerived n f →* alternatingGroup (Fin 5) :=
  (rootA5PreimageProjection n f).comp
    (rootA5PreimageDerived n f).subtype

/-- The derived subgroup of the full root preimage still maps onto `A₅`. -/
public theorem rootA5PreimageDerivedProjection_surjective
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f) :
    Function.Surjective (rootA5PreimageDerivedProjection n f) := by
  let E := rootA5Preimage n f
  let r := rootA5PreimageProjection n f
  have hrRange : r.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (rootA5PreimageProjection_surjective n f hsurj)
  have hmap : (commutator E).map r = ⊤ := by
    rw [map_commutator_eq, hrRange]
    exact Group.IsPerfect.commutator_eq_top
  intro y
  have hy : y ∈ (commutator E).map r := by
    rw [hmap]
    trivial
  obtain ⟨x, hx, hxy⟩ := hy
  exact ⟨⟨x, hx⟩, hxy⟩

/-- The derived root-preimage projection is again a central extension. -/
public theorem rootA5PreimageDerivedProjection_ker_le_center
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hker : f.ker ≤ Subgroup.center H) :
    (rootA5PreimageDerivedProjection n f).ker ≤
      Subgroup.center (rootA5PreimageDerived n f) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hx' : (x : rootA5Preimage n f) ∈
      (rootA5PreimageProjection n f).ker := hx
  exact Subgroup.mem_center_iff.mp
    (rootA5PreimageProjection_ker_le_center n f hker hx') y

/-- A1 33.18, local multiplier bound: the derived subgroup of the full
preimage of a standard root `A₅` is a covering of `A₅` whose kernel has order
at most two. -/
public theorem rootA5PreimageDerivedProjection_ker_card_le_two
    {H : Type*} [Group H] [Finite H]
    (n : Nat) (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Nat.card (rootA5PreimageDerivedProjection n f).ker ≤ 2 := by
  let D := rootA5PreimageDerived n f
  let r := rootA5PreimageProjection n f
  let rD := rootA5PreimageDerivedProjection n f
  let : Group.IsPerfect D :=
    commutator_isPerfect_of_surjective_of_ker_le_center
      r (rootA5PreimageProjection_surjective n f hsurj)
      (rootA5PreimageProjection_ker_le_center n f hker)
  let : Finite D := inferInstance
  have hrDsurj : Function.Surjective rD :=
    rootA5PreimageDerivedProjection_surjective n f hsurj
  have hrDcenter : rD.ker ≤ Subgroup.center D :=
    rootA5PreimageDerivedProjection_ker_le_center n f hker
  have hrDker : rD.ker = Subgroup.center D := by
    apply ker_eq_center_of_surjective_of_center_eq_bot rD hrDsurj hrDcenter
    exact alternatingGroup.center_eq_bot (by simp)
  let e : D ⧸ Subgroup.center D ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hrDker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective rD hrDsurj)
  let : IsQuasisimple D := {
    toIsPerfect := inferInstance
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
  }
  let c : Covering D (alternatingGroup (Fin 5)) := {
    toMonoidHom := rD
    surjective := hrDsurj
  }
  have hle := Covering.coveringKernel_card_le_of_universal
    (alternatingFreeCentralCovering 0)
    (alternatingFreeCentralCovering_isUniversal 0) c
  change Nat.card rD.ker ≤ 2
  rwa [natCard_ker_alternatingFreeCentralCovering_zero_eq_two] at hle

/-- The kernel of the root-preimage projection is the restriction of the
global kernel. -/
public theorem rootA5PreimageProjection_ker_eq_comap
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5))) :
    (rootA5PreimageProjection n f).ker =
      f.ker.comap (rootA5Preimage n f).subtype := by
  let r0 : rootA5Preimage n f →* rootA5 n :=
    (f.comp (rootA5Preimage n f).subtype).codRestrict
      (rootA5 n) (fun x => x.2)
  calc
    (rootA5PreimageProjection n f).ker = r0.ker :=
      MonoidHom.ker_comp_of_injective r0 (rootA5Equiv n).symm.toMonoidHom
        (rootA5Equiv n).symm.injective
    _ = f.ker.comap (rootA5Preimage n f).subtype := by
      ext x
      dsimp [r0]
      constructor
      · intro hx
        have hx0 := MonoidHom.mem_ker.mp hx
        have hfx : f x = 1 := congrArg Subtype.val hx0
        exact MonoidHom.mem_ker.mpr hfx
      · intro hx
        have hx' : (x : H) ∈ f.ker := hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hx'

/-- The kernel after restricting to the derived subgroup is the corresponding
subgroup intersection. -/
public theorem rootA5PreimageDerivedProjection_ker_eq_comap
    {H : Type*} [Group H] (n : Nat)
    (f : H →* alternatingGroup (Fin (n + 5))) :
    (rootA5PreimageDerivedProjection n f).ker =
      (rootA5PreimageProjection n f).ker.comap
        (rootA5PreimageDerived n f).subtype := by
  rfl

/-- If the global central kernel is a `p`-group for an odd prime, the derived
root `A₅` covering has trivial kernel. -/
public theorem rootA5PreimageDerivedProjection_ker_eq_bot_of_isPGroup
    {H : Type*} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (n : Nat) (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker) :
    (rootA5PreimageDerivedProjection n f).ker = ⊥ := by
  let rD := rootA5PreimageDerivedProjection n f
  have hkerpE : IsPGroup p
      (f.ker.comap (rootA5Preimage n f).subtype) :=
    hkerp.comap_subtype
  have hkerpD : IsPGroup p rD.ker := by
    rw [rootA5PreimageDerivedProjection_ker_eq_comap,
      rootA5PreimageProjection_ker_eq_comap]
    exact hkerpE.comap_subtype
  have hle : Nat.card rD.ker ≤ 2 :=
    rootA5PreimageDerivedProjection_ker_card_le_two n f hsurj hker
  have hcard : Nat.card rD.ker = 1 := by
    rcases hkerpD.card_eq_or_dvd with h1 | hp
    · exact h1
    · have hpos : 0 < Nat.card rD.ker := Nat.card_pos
      have hp_le : p ≤ 2 := le_trans (Nat.le_of_dvd hpos hp) hle
      have hp_ge : 2 ≤ p := (Fact.out : p.Prime).two_le
      exact False.elim (hp2 (Nat.le_antisymm hp_le hp_ge))
  exact Subgroup.card_eq_one.mp hcard

/-- A1 33.18, splitting core: for an odd-primary central kernel, the global
kernel and the derived subgroup of the full root `A₅` preimage are
complementary. -/
public theorem rootA5PreimageProjection_ker_isComplement'_derived_of_isPGroup
    {H : Type*} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (n : Nat) (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker) :
    (rootA5PreimageProjection n f).ker.IsComplement'
      (rootA5PreimageDerived n f) := by
  let E := rootA5Preimage n f
  let r := rootA5PreimageProjection n f
  let D := rootA5PreimageDerived n f
  let rD := rootA5PreimageDerivedProjection n f
  have hkerD : rD.ker = ⊥ :=
    rootA5PreimageDerivedProjection_ker_eq_bot_of_isPGroup
      hp2 n f hsurj hker hkerp
  have hdisj : Disjoint r.ker D := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxD
    let d : D := ⟨x, hxD⟩
    have hdker : d ∈ rD.ker := by
      rw [MonoidHom.mem_ker]
      exact MonoidHom.mem_ker.mp hxK
    have hd1 : d = 1 := by
      rw [hkerD] at hdker
      exact Subgroup.mem_bot.mp hdker
    exact congrArg Subtype.val hd1
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨d, hd⟩ :=
    rootA5PreimageDerivedProjection_surjective n f hsurj (r x)
  apply Set.mem_mul.mpr
  refine ⟨x * (d : E)⁻¹, ?_, d, d.2, ?_⟩
  · change x * (d : E)⁻¹ ∈ r.ker
    have hd' : r (d : E) = r x := hd
    rw [MonoidHom.mem_ker, map_mul, map_inv, hd']
    simp
  · simp

/-- Every element of the root `A₅` has an order-preserving lift in the derived
factor when the global central kernel is odd-primary. -/
public theorem exists_rootA5PreimageDerived_lift_orderOf_eq_of_isPGroup
    {H : Type*} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (n : Nat) (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (a : alternatingGroup (Fin 5)) :
    ∃ y : rootA5PreimageDerived n f,
      rootA5PreimageDerivedProjection n f y = a ∧ orderOf y = orderOf a := by
  let rD := rootA5PreimageDerivedProjection n f
  have hkerD : rD.ker = ⊥ :=
    rootA5PreimageDerivedProjection_ker_eq_bot_of_isPGroup
      hp2 n f hsurj hker hkerp
  have hinj : Function.Injective rD := rD.ker_eq_bot_iff.mp hkerD
  obtain ⟨y, hy⟩ :=
    rootA5PreimageDerivedProjection_surjective n f hsurj a
  refine ⟨y, hy, ?_⟩
  have hord := orderOf_injective rD hinj y
  rw [hy] at hord
  exact hord.symm

/-- Direct-product form of the A1 33.18 splitting: multiplication identifies
the root-preimage kernel times the derived root `A₅` with the whole root
preimage. -/
public noncomputable def rootA5PreimageKernelProdDerivedMulEquiv
    {H : Type*} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (n : Nat) (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker) :
    (rootA5PreimageProjection n f).ker × rootA5PreimageDerived n f ≃*
      rootA5Preimage n f := by
  let E := rootA5Preimage n f
  let K := (rootA5PreimageProjection n f).ker
  let D := rootA5PreimageDerived n f
  let m : K × D →* E := {
    toFun := fun x => (x.1 : E) * (x.2 : E)
    map_one' := by simp
    map_mul' := by
      intro a b
      have hb1 : (b.1 : E) ∈ Subgroup.center E :=
        rootA5PreimageProjection_ker_le_center n f hker b.1.2
      have hc : (a.2 : E) * (b.1 : E) = (b.1 : E) * (a.2 : E) :=
        Subgroup.mem_center_iff.mp hb1 (a.2 : E)
      change ((a.1 : E) * (b.1 : E)) * ((a.2 : E) * (b.2 : E)) =
        ((a.1 : E) * (a.2 : E)) * ((b.1 : E) * (b.2 : E))
      calc
        _ = (a.1 : E) * ((b.1 : E) * (a.2 : E)) * (b.2 : E) := by
          simp only [mul_assoc]
        _ = (a.1 : E) * ((a.2 : E) * (b.1 : E)) * (b.2 : E) := by
          rw [← hc]
        _ = _ := by simp only [mul_assoc]
  }
  apply MulEquiv.ofBijective m
  exact rootA5PreimageProjection_ker_isComplement'_derived_of_isPGroup
    hp2 n f hsurj hker hkerp

/-- A1 33.18 in cyclic-preimage form: the preimage of any cyclic subgroup of
the root `A₅` is generated by the central kernel and an order-preserving lift
inside the derived direct factor. -/
public theorem exists_rootA5CyclicPreimage_eq_ker_sup_zpowers_of_isPGroup
    {H : Type*} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (n : Nat) (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (a : alternatingGroup (Fin 5)) :
    ∃ y : rootA5PreimageDerived n f,
      rootA5PreimageDerivedProjection n f y = a ∧
      orderOf y = orderOf a ∧
      (Subgroup.zpowers a).comap (rootA5PreimageProjection n f) =
        (rootA5PreimageProjection n f).ker ⊔
          Subgroup.zpowers (y : rootA5Preimage n f) := by
  obtain ⟨y, hy, hord⟩ :=
    exists_rootA5PreimageDerived_lift_orderOf_eq_of_isPGroup
      hp2 n f hsurj hker hkerp a
  refine ⟨y, hy, hord, ?_⟩
  let E := rootA5Preimage n f
  let r := rootA5PreimageProjection n f
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    let yk : E := (y : E) ^ k
    have hyk : r yk = r x := by
      rw [map_zpow]
      change rootA5PreimageDerivedProjection n f y ^ k = r x
      rw [hy, hk]
    have hxker : x * yk⁻¹ ∈ r.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyk]
      simp
    have hyzp : yk ∈ Subgroup.zpowers (y : E) :=
      (Subgroup.zpowers (y : E)).zpow_mem (Subgroup.mem_zpowers _) k
    have hprod := Subgroup.mul_mem _
      (show x * yk⁻¹ ∈ r.ker ⊔ Subgroup.zpowers (y : E) from
        Subgroup.mem_sup_left hxker)
      (show yk ∈ r.ker ⊔ Subgroup.zpowers (y : E) from
        Subgroup.mem_sup_right hyzp)
    simpa [yk, mul_assoc] using hprod
  · intro hx
    have hleft : r.ker ≤ (Subgroup.zpowers a).comap r := by
      intro z hz
      have hz1 : r z = 1 := MonoidHom.mem_ker.mp hz
      change r z ∈ Subgroup.zpowers a
      rw [hz1]
      exact (Subgroup.zpowers a).one_mem
    have hright : Subgroup.zpowers (y : E) ≤
        (Subgroup.zpowers a).comap r := by
      rw [Subgroup.zpowers_le]
      change r (y : E) ∈ Subgroup.zpowers a
      rw [show r (y : E) = a from hy]
      exact Subgroup.mem_zpowers a
    exact (show r.ker ⊔ Subgroup.zpowers (y : E) ≤
      (Subgroup.zpowers a).comap r from sup_le hleft hright) hx

end GLS3.Chapter5.SchurPresentation
/- END Theory.RootSubextension -/

/- BEGIN Theory.AlternatingCentralizerSignKernel -/
noncomputable section

namespace GLS3.Chapter5

/-- The even part of the symmetric-group centralizer of a permutation is the
fixed-point subgroup of the induced automorphism of the alternating group. -/
@[expose]
public noncomputable def alternatingCentralizerSignKernelEquivFixedConjNormal
    {n : Nat} (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.sign.comp
        (Subgroup.subtype (Subgroup.centralizer
          ({σ} : Set (Equiv.Perm (Fin n)))))).ker ≃*
      automorphismFixedSubgroup
        (MulAut.conjNormal (H := alternatingGroup (Fin n)) σ) where
  toFun z := ⟨⟨z.1.1, by
    rw [Equiv.Perm.mem_alternatingGroup]
    exact MonoidHom.mem_ker.mp z.2⟩, by
      change (MulAut.conjNormal σ) ⟨z.1.1, _⟩ = ⟨z.1.1, _⟩
      apply Subtype.ext
      change σ * z.1.1 * σ⁻¹ = z.1.1
      have hcomm : Commute z.1.1 σ :=
        Subgroup.mem_centralizer_singleton_iff.mp z.1.2
      rw [hcomm.eq.symm, mul_inv_cancel_right]⟩
  invFun g := ⟨⟨g.1.1, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfix := g.2
    change (MulAut.conjNormal σ) g.1 = g.1 at hfix
    have h := congrArg (fun q : alternatingGroup (Fin n) ↦ q.1 * σ) hfix
    have hA : g.1.1 * σ = σ * g.1.1 := by simpa [mul_assoc] using h.symm
    exact hA⟩, by
      rw [MonoidHom.mem_ker]
      exact g.1.2⟩
  left_inv z := by ext; rfl
  right_inv g := by ext; rfl
  map_mul' _ _ := rfl

/-- Inner-conjugation specialization of
`alternatingCentralizerSignKernelEquivFixedConjNormal`. -/
public noncomputable def alternatingCentralizerSignKernelEquivFixed
    {n : Nat} (a : alternatingGroup (Fin n)) :
    (Equiv.Perm.sign.comp
        (Subgroup.subtype (Subgroup.centralizer
          ({(a : Equiv.Perm (Fin n))} : Set (Equiv.Perm (Fin n)))))).ker ≃*
      automorphismFixedSubgroup (MulAut.conj a) := by
  rw [← MulAut.conjNormal_val (h := a)]
  exact alternatingCentralizerSignKernelEquivFixedConjNormal
    (a : Equiv.Perm (Fin n))

end GLS3.Chapter5
/- END Theory.AlternatingCentralizerSignKernel -/

/- BEGIN Theory.InvolutionCycleSwapSupportEq -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionCycleSwapSupportEq_u

public theorem involutionCycleSwap_support_eq_union
    {Ω : Type __ch5_InvolutionCycleSwapSupportEq_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    let l := e.symm (Equiv.swap c d)
    l.1.1.support = c.1.support ∪ d.1.support := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  let l := e.symm (Equiv.swap c d)
  rcases l.2 with ⟨q, hq⟩
  rw [← hq]
  change (Equiv.Perm.Basis.ofPermHom
    (Classical.choice (Equiv.Perm.Basis.nonempty x))
    (cycleActionRangeToExplicitRange x q)).support = _
  rw [Equiv.Perm.Basis.ofPermHom_support]
  have hqval : (q : Equiv.Perm x.cycleFactorsFinset) = Equiv.swap c d := by
    have hel := e.apply_symm_apply (Equiv.swap c d)
    let e1 := cycleActionRangeMulEquivCyclePermutationSubgroup x
    let e2 := cycleActionRangeMulEquivPermOfPrimeOrder x hp
    have he1 : e1 q = l := by
      apply Subtype.ext
      exact hq
    have hqinv : e1.symm l = q := by
      rw [← he1]
      exact e1.symm_apply_apply q
    calc
      (q : Equiv.Perm x.cycleFactorsFinset) = e2 q := rfl
      _ = e2 (e1.symm l) := congrArg e2 hqinv.symm
      _ = e l := rfl
      _ = Equiv.swap c d := hel
  change (q : Equiv.Perm x.cycleFactorsFinset).support.biUnion
    (fun k => k.1.support) = _
  rw [hqval, Equiv.Perm.support_swap hcd]
  ext ω
  simp

end GLS3.Chapter5
/- END Theory.InvolutionCycleSwapSupportEq -/

/- BEGIN Theory.BlockExtension -/
universe __ch5_BlockExtension_u __ch5_BlockExtension_v

noncomputable section

/- Source: CentralProductExtension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement Pointwise

/-! ## Central extensions of direct products

For a central extension of a product of perfect groups, restrict to the full
preimages of the two factors and then to their derived subgroups.  If those two
derived coverings have trivial kernels, their inverse sections commute and
combine to a section of the product.  The alternating-group specialization
below bounds each component kernel by the corresponding Schur multiplier.
-/


private theorem __ch5_BlockExtension_map_eq_one_of_isPerfect_to_commGroup
    {A : Type __ch5_BlockExtension_u} {C : Type __ch5_BlockExtension_v} [Group A] [CommGroup C] [Group.IsPerfect A]
    (f : A →* C) (a : A) : f a = 1 := by
  apply MonoidHom.mem_ker.mp
  exact Abelianization.commutator_subset_ker f
    (Group.IsPerfect.mem_commutator (g := a))

/-- The left direct factor `A × 1` as a subgroup of `A × B`. -/
@[expose] public def prodLeftFactor (A B : Type*) [Group A] [Group B] : Subgroup (A × B) :=
  (⊤ : Subgroup A).prod ⊥

/-- The right direct factor `1 × B` as a subgroup of `A × B`. -/
@[expose] public def prodRightFactor (A B : Type*) [Group A] [Group B] : Subgroup (A × B) :=
  (⊥ : Subgroup A).prod ⊤

/-- The full preimage of the left direct factor. -/
public abbrev prodLeftPreimage
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) : Subgroup H :=
  (prodLeftFactor A B).comap f

/-- The full preimage of the right direct factor. -/
public abbrev prodRightPreimage
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) : Subgroup H :=
  (prodRightFactor A B).comap f

/-- Projection from the full left-factor preimage to `A`. -/
@[expose] public def prodLeftPreimageProjection
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) : prodLeftPreimage f →* A :=
  (MonoidHom.fst A B).comp (f.comp (prodLeftPreimage f).subtype)

/-- Projection from the full right-factor preimage to `B`. -/
@[expose] public def prodRightPreimageProjection
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) : prodRightPreimage f →* B :=
  (MonoidHom.snd A B).comp (f.comp (prodRightPreimage f).subtype)

/-- The left-factor preimage projection is surjective. -/
public theorem prodLeftPreimageProjection_surjective
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) (hf : Function.Surjective f) :
    Function.Surjective (prodLeftPreimageProjection f) := by
  intro a
  obtain ⟨x, hx⟩ := hf (a, 1)
  have hxE : x ∈ prodLeftPreimage f := by
    change f x ∈ (⊤ : Subgroup A).prod ⊥
    rw [hx]
    exact ⟨Subgroup.mem_top a, Subgroup.mem_bot.mpr rfl⟩
  exact ⟨⟨x, hxE⟩, congrArg Prod.fst hx⟩

/-- The right-factor preimage projection is surjective. -/
public theorem prodRightPreimageProjection_surjective
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) (hf : Function.Surjective f) :
    Function.Surjective (prodRightPreimageProjection f) := by
  intro b
  obtain ⟨x, hx⟩ := hf (1, b)
  have hxE : x ∈ prodRightPreimage f := by
    change f x ∈ (⊥ : Subgroup A).prod ⊤
    rw [hx]
    exact ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top b⟩
  exact ⟨⟨x, hxE⟩, congrArg Prod.snd hx⟩

/-- A central global kernel induces a central left-factor kernel. -/
public theorem prodLeftPreimageProjection_ker_le_center
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) (hker : f.ker ≤ Subgroup.center H) :
    (prodLeftPreimageProjection f).ker ≤
      Subgroup.center (prodLeftPreimage f) := by
  intro x hx
  have hfst : (f (x : H)).1 = 1 := MonoidHom.mem_ker.mp hx
  have hsnd : (f (x : H)).2 = 1 := by
    have hxE := x.2
    exact Subgroup.mem_bot.mp hxE.2
  have hxker : (x : H) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact Prod.ext hfst hsnd
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hxker) y.1

/-- A central global kernel induces a central right-factor kernel. -/
public theorem prodRightPreimageProjection_ker_le_center
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) (hker : f.ker ≤ Subgroup.center H) :
    (prodRightPreimageProjection f).ker ≤
      Subgroup.center (prodRightPreimage f) := by
  intro x hx
  have hsnd : (f (x : H)).2 = 1 := MonoidHom.mem_ker.mp hx
  have hfst : (f (x : H)).1 = 1 := by
    have hxE := x.2
    exact Subgroup.mem_bot.mp hxE.1
  have hxker : (x : H) ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    exact Prod.ext hfst hsnd
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hxker) y.1

/-- The left-factor preimage kernel is the restriction of the global kernel. -/
public theorem prodLeftPreimageProjection_ker_eq_comap
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) :
    (prodLeftPreimageProjection f).ker =
      f.ker.comap (prodLeftPreimage f).subtype := by
  ext x
  constructor
  · intro hx
    have hfst : (f (x : H)).1 = 1 := MonoidHom.mem_ker.mp hx
    have hsnd : (f (x : H)).2 = 1 := Subgroup.mem_bot.mp x.2.2
    exact MonoidHom.mem_ker.mpr (Prod.ext hfst hsnd)
  · intro hx
    exact MonoidHom.mem_ker.mpr
      (congrArg Prod.fst (MonoidHom.mem_ker.mp hx))

/-- The right-factor preimage kernel is the restriction of the global kernel. -/
public theorem prodRightPreimageProjection_ker_eq_comap
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) :
    (prodRightPreimageProjection f).ker =
      f.ker.comap (prodRightPreimage f).subtype := by
  ext x
  constructor
  · intro hx
    have hfst : (f (x : H)).1 = 1 := Subgroup.mem_bot.mp x.2.1
    have hsnd : (f (x : H)).2 = 1 := MonoidHom.mem_ker.mp hx
    exact MonoidHom.mem_ker.mpr (Prod.ext hfst hsnd)
  · intro hx
    exact MonoidHom.mem_ker.mpr
      (congrArg Prod.snd (MonoidHom.mem_ker.mp hx))

/-- The derived subgroup of the full left-factor preimage. -/
public abbrev prodLeftPreimageDerived
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) := commutator (prodLeftPreimage f)

/-- The derived subgroup of the full right-factor preimage. -/
public abbrev prodRightPreimageDerived
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) := commutator (prodRightPreimage f)

/-- The left-factor projection restricted to the derived subgroup. -/
@[expose] public def prodLeftPreimageDerivedProjection
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) : prodLeftPreimageDerived f →* A :=
  (prodLeftPreimageProjection f).comp (prodLeftPreimageDerived f).subtype

/-- The right-factor projection restricted to the derived subgroup. -/
@[expose] public def prodRightPreimageDerivedProjection
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) : prodRightPreimageDerived f →* B :=
  (prodRightPreimageProjection f).comp (prodRightPreimageDerived f).subtype

/-- The left derived kernel is the restriction of the left preimage kernel. -/
public theorem prodLeftPreimageDerivedProjection_ker_eq_comap
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) :
    (prodLeftPreimageDerivedProjection f).ker =
      (prodLeftPreimageProjection f).ker.comap
        (prodLeftPreimageDerived f).subtype := by
  rfl

/-- The right derived kernel is the restriction of the right preimage kernel. -/
public theorem prodRightPreimageDerivedProjection_ker_eq_comap
    {H A B : Type*} [Group H] [Group A] [Group B]
    (f : H →* A × B) :
    (prodRightPreimageDerivedProjection f).ker =
      (prodRightPreimageProjection f).ker.comap
        (prodRightPreimageDerived f).subtype := by
  rfl

/-- Perfectness of `A` makes the left derived projection surjective. -/
public theorem prodLeftPreimageDerivedProjection_surjective
    {H A B : Type*} [Group H] [Group A] [Group B] [Group.IsPerfect A]
    (f : H →* A × B) (hf : Function.Surjective f) :
    Function.Surjective (prodLeftPreimageDerivedProjection f) := by
  let r := prodLeftPreimageProjection f
  have hrange : r.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (prodLeftPreimageProjection_surjective f hf)
  have hmap : (commutator (prodLeftPreimage f)).map r = ⊤ := by
    rw [map_commutator_eq, hrange]
    exact Group.IsPerfect.commutator_eq_top
  intro a
  have ha : a ∈ (commutator (prodLeftPreimage f)).map r := by rw [hmap]; trivial
  obtain ⟨x, hx, hxa⟩ := ha
  exact ⟨⟨x, hx⟩, hxa⟩

/-- Perfectness of `B` makes the right derived projection surjective. -/
public theorem prodRightPreimageDerivedProjection_surjective
    {H A B : Type*} [Group H] [Group A] [Group B] [Group.IsPerfect B]
    (f : H →* A × B) (hf : Function.Surjective f) :
    Function.Surjective (prodRightPreimageDerivedProjection f) := by
  let r := prodRightPreimageProjection f
  have hrange : r.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (prodRightPreimageProjection_surjective f hf)
  have hmap : (commutator (prodRightPreimage f)).map r = ⊤ := by
    rw [map_commutator_eq, hrange]
    exact Group.IsPerfect.commutator_eq_top
  intro b
  have hb : b ∈ (commutator (prodRightPreimage f)).map r := by rw [hmap]; trivial
  obtain ⟨x, hx, hxb⟩ := hb
  exact ⟨⟨x, hx⟩, hxb⟩

set_option backward.isDefEq.respectTransparency false in
/-- The derived kernel of any finite central extension of `A_{q+5}` has order
dividing the order of the universal alternating covering kernel. -/
public theorem alternatingCentralExtensionDerived_ker_card_dvd_multiplier
    {E : Type} [Group E] [Finite E]
    (q : Nat)
    (r : E →* alternatingGroup (Fin (q + 5)))
    (hr : Function.Surjective r)
    (hker : r.ker ≤ Subgroup.center E) :
    Nat.card (r.comp (commutator E).subtype).ker ∣
      Nat.card (alternatingFreeCentralCovering q).toMonoidHom.ker := by
  let D := commutator E
  let rD := r.comp D.subtype
  let : Group.IsPerfect D :=
    commutator_isPerfect_of_surjective_of_ker_le_center r hr hker
  let : Finite D := inferInstance
  have hrDsurj : Function.Surjective rD := by
    have hmap : D.map r = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hr]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ D.map r := by rw [hmap]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have hrDcenter : rD.ker ≤ Subgroup.center D := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker hx) y
  have hrDker : rD.ker = Subgroup.center D := by
    apply ker_eq_center_of_surjective_of_center_eq_bot rD hrDsurj hrDcenter
    exact alternatingGroup.center_eq_bot (by simp)
  let e : D ⧸ Subgroup.center D ≃*
      alternatingGroup (Fin (q + 5)) :=
    (QuotientGroup.quotientMulEquivOfEq hrDker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective rD hrDsurj)
  let : IsQuasisimple D := {
    toIsPerfect := inferInstance
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin (q + 5))) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
  }
  let c : Covering D (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := rD
    surjective := hrDsurj
  }
  exact Covering.coveringKernel_card_dvd_of_universal
    (alternatingFreeCentralCovering q)
    (alternatingFreeCentralCovering_isUniversal q) c

/-- If the global kernel is a `p`-group and the left alternating multiplier
has no `p`-part, the left component derived covering has trivial kernel. -/
public theorem
    prodLeftPreimageDerivedProjection_ker_eq_bot_of_not_dvd_multiplier
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin (qA + 5)) ×
      alternatingGroup (Fin (qB + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker) :
    (prodLeftPreimageDerivedProjection f).ker = ⊥ := by
  let rD := prodLeftPreimageDerivedProjection f
  have hkerpE : IsPGroup p
      (f.ker.comap (prodLeftPreimage f).subtype) :=
    hkerp.comap_subtype
  have hkerpD : IsPGroup p rD.ker := by
    rw [prodLeftPreimageDerivedProjection_ker_eq_comap,
      prodLeftPreimageProjection_ker_eq_comap]
    exact hkerpE.comap_subtype
  have hdvd : Nat.card rD.ker ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker :=
    alternatingCentralExtensionDerived_ker_card_dvd_multiplier qA
      (prodLeftPreimageProjection f)
      (prodLeftPreimageProjection_surjective f hf)
      (prodLeftPreimageProjection_ker_le_center f hker)
  have hcard : Nat.card rD.ker = 1 := by
    rcases hkerpD.card_eq_or_dvd with h1 | hp
    · exact h1
    · exact False.elim (hpM (hp.trans hdvd))
  exact Subgroup.card_eq_one.mp hcard

/-- If the global kernel is a `p`-group and the right alternating multiplier
has no `p`-part, the right component derived covering has trivial kernel. -/
public theorem
    prodRightPreimageDerivedProjection_ker_eq_bot_of_not_dvd_multiplier
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin (qA + 5)) ×
      alternatingGroup (Fin (qB + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker) :
    (prodRightPreimageDerivedProjection f).ker = ⊥ := by
  let rD := prodRightPreimageDerivedProjection f
  have hkerpE : IsPGroup p
      (f.ker.comap (prodRightPreimage f).subtype) :=
    hkerp.comap_subtype
  have hkerpD : IsPGroup p rD.ker := by
    rw [prodRightPreimageDerivedProjection_ker_eq_comap,
      prodRightPreimageProjection_ker_eq_comap]
    exact hkerpE.comap_subtype
  have hdvd : Nat.card rD.ker ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker :=
    alternatingCentralExtensionDerived_ker_card_dvd_multiplier qB
      (prodRightPreimageProjection f)
      (prodRightPreimageProjection_surjective f hf)
      (prodRightPreimageProjection_ker_le_center f hker)
  have hcard : Nat.card rD.ker = 1 := by
    rcases hkerpD.card_eq_or_dvd with h1 | hp
    · exact h1
    · exact False.elim (hpM (hp.trans hdvd))
  exact Subgroup.card_eq_one.mp hcard

private theorem __ch5_BlockExtension_commutatorElement_eq_one_of_left_perfect_of_mem_center
    {A H : Type*} [Group A] [Group H] [Group.IsPerfect A]
    (s : A →* H) (y : H)
    (hc : ∀ a : A, ⁅s a, y⁆ ∈ Subgroup.center H)
    (a : A) : ⁅s a, y⁆ = 1 := by
  let : CommGroup (Subgroup.center H) := {
    mul_comm := fun x z => Subtype.ext
      (Subgroup.mem_center_iff.mp x.2 z.1).symm }
  let φ : A →* Subgroup.center H := {
    toFun := fun x => ⟨⁅s x, y⁆, hc x⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro a₁ a₂
      apply Subtype.ext
      change ⁅s (a₁ * a₂), y⁆ = ⁅s a₁, y⁆ * ⁅s a₂, y⁆
      rw [map_mul, commutatorElement_mul_left_eq_conj_mul]
      have hc₂ := hc a₂
      have hconj : s a₁ * ⁅s a₂, y⁆ * (s a₁)⁻¹ = ⁅s a₂, y⁆ := by
        have hcomm := Subgroup.mem_center_iff.mp hc₂ (s a₁)
        rw [hcomm]
        simp
      rw [hconj]
      exact (Subgroup.mem_center_iff.mp hc₂ ⁅s a₁, y⁆).symm
  }
  exact congrArg Subtype.val
    (__ch5_BlockExtension_map_eq_one_of_isPerfect_to_commGroup
      (A := A) (C := Subgroup.center H) φ a)

set_option backward.isDefEq.respectTransparency false in
/-- A central extension of a product of perfect groups splits if the two
component derived coverings have trivial kernels. -/
public theorem exists_prod_section_isComplement'_of_component_derived_ker_eq_bot
    {H A B : Type*} [Group H] [Group A] [Group B]
    [Group.IsPerfect A] [Group.IsPerfect B]
    (f : H →* A × B) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hleft : (prodLeftPreimageDerivedProjection f).ker = ⊥)
    (hright : (prodRightPreimageDerivedProjection f).ker = ⊥) :
    ∃ s : A × B →* H,
      f.comp s = MonoidHom.id (A × B) ∧ f.ker.IsComplement' s.range := by
  let EL := prodLeftPreimage f
  let ER := prodRightPreimage f
  let DL := prodLeftPreimageDerived f
  let DR := prodRightPreimageDerived f
  let rL := prodLeftPreimageDerivedProjection f
  let rR := prodRightPreimageDerivedProjection f
  have hrLbij : Function.Bijective rL :=
    ⟨rL.ker_eq_bot_iff.mp hleft,
      prodLeftPreimageDerivedProjection_surjective f hf⟩
  have hrRbij : Function.Bijective rR :=
    ⟨rR.ker_eq_bot_iff.mp hright,
      prodRightPreimageDerivedProjection_surjective f hf⟩
  let eL : DL ≃* A := MulEquiv.ofBijective rL hrLbij
  let eR : DR ≃* B := MulEquiv.ofBijective rR hrRbij
  let sL : A →* H :=
    (EL.subtype.comp DL.subtype).comp eL.symm.toMonoidHom
  let sR : B →* H :=
    (ER.subtype.comp DR.subtype).comp eR.symm.toMonoidHom
  have hsL (a : A) : f (sL a) = (a, 1) := by
    apply Prod.ext
    · change rL (eL.symm a) = a
      exact eL.apply_symm_apply a
    · have hmem := (eL.symm a : DL).1.2
      exact Subgroup.mem_bot.mp hmem.2
  have hsR (b : B) : f (sR b) = (1, b) := by
    apply Prod.ext
    · have hmem := (eR.symm b : DR).1.2
      exact Subgroup.mem_bot.mp hmem.1
    · change rR (eR.symm b) = b
      exact eR.apply_symm_apply b
  have hcommKer (a : A) (b : B) : ⁅sL a, sR b⁆ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hsL, hsR]
    simp [commutatorElement_def]
  have hcommCenter (a : A) (b : B) : ⁅sL a, sR b⁆ ∈ Subgroup.center H :=
    hker (hcommKer a b)
  have hcommOne (a : A) (b : B) : ⁅sL a, sR b⁆ = 1 := by
    exact __ch5_BlockExtension_commutatorElement_eq_one_of_left_perfect_of_mem_center
      sL (sR b) (fun x => hcommCenter x b) a
  have hcommute (a : A) (b : B) : Commute (sL a) (sR b) :=
    commutatorElement_eq_one_iff_commute.mp (hcommOne a b)
  let s : A × B →* H := {
    toFun := fun x => sL x.1 * sR x.2
    map_one' := by simp
    map_mul' := by
      intro x y
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
      calc
        (sL x.1 * sL y.1) * (sR x.2 * sR y.2) =
            sL x.1 * (sL y.1 * sR x.2) * sR y.2 := by
          simp only [mul_assoc]
        _ = sL x.1 * (sR x.2 * sL y.1) * sR y.2 := by
          rw [(hcommute y.1 x.2).eq]
        _ = _ := by simp only [mul_assoc]
  }
  have hsec : f.comp s = MonoidHom.id (A × B) := by
    apply MonoidHom.ext
    intro x
    change f (sL x.1 * sR x.2) = x
    rw [map_mul, hsL, hsR]
    exact Prod.ext (by simp) (by simp)
  have hdisj : Disjoint f.ker s.range := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    obtain ⟨y, rfl⟩ := hxR
    have hy : y = 1 := by
      have hxy : f (s y) = y := DFunLike.congr_fun hsec y
      have hfone : f (s y) = 1 := MonoidHom.mem_ker.mp hxK
      exact hxy.symm.trans hfone
    rw [hy]
    exact map_one s
  have hmul : (f.ker : Set H) * (s.range : Set H) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    let y := s (f x)
    let k := x * y⁻¹
    have hyf : f y = f x := by
      have hxy : f (s (f x)) = f x := DFunLike.congr_fun hsec (f x)
      exact hxy
    have hk : k ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [k]
      rw [map_mul, map_inv, hyf]
      simp
    have hy : y ∈ s.range := ⟨f x, rfl⟩
    apply Set.mem_mul.mpr
    exact ⟨k, hk, y, hy, by simp [k]⟩
  exact ⟨s, hsec,
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul⟩

/-- Alternating specialization of the direct-product splitting criterion:
absence of a `p`-part in both factor multipliers produces a section and a
complement to the global `p`-primary central kernel. -/
public theorem exists_prod_section_isComplement'_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin (qA + 5)) ×
      alternatingGroup (Fin (qB + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker) :
    ∃ s : alternatingGroup (Fin (qA + 5)) ×
        alternatingGroup (Fin (qB + 5)) →* H,
      f.comp s = MonoidHom.id _ ∧ f.ker.IsComplement' s.range := by
  apply exists_prod_section_isComplement'_of_component_derived_ker_eq_bot
    f hf hker
  · exact prodLeftPreimageDerivedProjection_ker_eq_bot_of_not_dvd_multiplier
      qA qB f hf hker hkerp hpMA
  · exact prodRightPreimageDerivedProjection_ker_eq_bot_of_not_dvd_multiplier
      qA qB f hf hker hkerp hpMB

end GLS3.Chapter5.SchurPresentation

/- Source: BlockSubextension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Two-block alternating subextensions

This file realizes the block-diagonal inclusion `A_a × A_b ↪ A_{a+b}` and
restricts a central extension of `A_{a+b}` to its full preimage.  The final
theorem applies the central-product splitting criterion when both smaller
alternating multipliers have no `p`-part.
-/

/-- Block-diagonal inclusion on a sum of two finite types. -/
public def alternatingProdSumHom
    (α β : Type*) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] :
    alternatingGroup α × alternatingGroup β →*
      alternatingGroup (α ⊕ β) where
  toFun x := ⟨Equiv.Perm.sumCongr x.1.1 x.2.1, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_sumCongr]
    have hx1 := x.1.2
    have hx2 := x.2.2
    rw [Equiv.Perm.mem_alternatingGroup] at hx1 hx2
    simp [hx1, hx2]⟩
  map_one' := by
    apply Subtype.ext
    exact Equiv.Perm.sumCongr_one
  map_mul' x y := by
    apply Subtype.ext
    exact (Equiv.Perm.sumCongr_mul x.1.1 x.2.1 y.1.1 y.2.1).symm

public theorem alternatingProdSumHom_injective
    (α β : Type*) [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] :
    Function.Injective (alternatingProdSumHom α β) := by
  intro x y hxy
  have hval : Equiv.Perm.sumCongr x.1.1 x.2.1 =
      Equiv.Perm.sumCongr y.1.1 y.2.1 := congrArg Subtype.val hxy
  have hpair : (x.1.1, x.2.1) = (y.1.1, y.2.1) :=
    Equiv.Perm.sumCongrHom_injective hval
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hpair)
  · exact Subtype.ext (congrArg Prod.snd hpair)

@[expose] public def alternatingProdBlockHom (a b : Nat) :
    alternatingGroup (Fin a) × alternatingGroup (Fin b) →*
      alternatingGroup (Fin (a + b)) :=
  (finSumFinEquiv.altCongrHom).toMonoidHom.comp
    (alternatingProdSumHom (Fin a) (Fin b))

public theorem alternatingProdBlockHom_injective (a b : Nat) :
    Function.Injective (alternatingProdBlockHom a b) := by
  exact finSumFinEquiv.altCongrHom.injective.comp
    (alternatingProdSumHom_injective (Fin a) (Fin b))

/-- The full symmetric two-block embedding `S_a × S_b ↪ S_{a+b}`. -/
@[expose] public def permProdBlockHom (a b : Nat) :
    Equiv.Perm (Fin a) × Equiv.Perm (Fin b) →*
      Equiv.Perm (Fin (a + b)) :=
  finSumFinEquiv.permCongrHom.toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin a) (Fin b))

/-- The symmetric two-block embedding is injective. -/
public theorem permProdBlockHom_injective (a b : Nat) :
    Function.Injective (permProdBlockHom a b) :=
  finSumFinEquiv.permCongrHom.injective.comp
    Equiv.Perm.sumCongrHom_injective

/-- Evaluation formula for the symmetric two-block embedding. -/
@[simp]
public theorem permProdBlockHom_apply (a b : Nat)
    (x : Equiv.Perm (Fin a) × Equiv.Perm (Fin b)) :
    permProdBlockHom a b x =
      finSumFinEquiv.permCongr (Equiv.Perm.sumCongr x.1 x.2) := by
  rfl

/-- The underlying permutation of the alternating block embedding is the
corresponding symmetric block embedding. -/
@[simp]
public theorem coe_alternatingProdBlockHom_apply (a b : Nat)
    (x : alternatingGroup (Fin a) × alternatingGroup (Fin b)) :
    ((alternatingProdBlockHom a b x : alternatingGroup (Fin (a + b))) :
      Equiv.Perm (Fin (a + b))) =
      permProdBlockHom a b ((x.1 : Equiv.Perm (Fin a)),
        (x.2 : Equiv.Perm (Fin b))) := by
  rfl

public abbrev alternatingBlockPreimage
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) : Subgroup H :=
  (alternatingProdBlockHom a b).range.comap f

@[expose] public def alternatingBlockPreimageProjection
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    alternatingBlockPreimage a b f →*
      alternatingGroup (Fin a) × alternatingGroup (Fin b) :=
  let i := alternatingProdBlockHom a b
  let e := MonoidHom.ofInjective (alternatingProdBlockHom_injective a b)
  e.symm.toMonoidHom.comp
    ((f.comp (alternatingBlockPreimage a b f).subtype).codRestrict
      i.range (fun x => x.2))

public theorem alternatingBlockPreimageProjection_surjective
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hf : Function.Surjective f) :
    Function.Surjective (alternatingBlockPreimageProjection a b f) := by
  intro y
  let i := alternatingProdBlockHom a b
  let e := MonoidHom.ofInjective (alternatingProdBlockHom_injective a b)
  obtain ⟨x, hx⟩ := hf (i y)
  have hxE : x ∈ alternatingBlockPreimage a b f := by
    exact ⟨y, hx.symm⟩
  let xE : alternatingBlockPreimage a b f := ⟨x, hxE⟩
  refine ⟨xE, ?_⟩
  change e.symm ⟨f x, hxE⟩ = y
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact hx

public theorem alternatingBlockPreimageProjection_ker_eq_comap
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b))) :
    (alternatingBlockPreimageProjection a b f).ker =
      f.ker.comap (alternatingBlockPreimage a b f).subtype := by
  let i := alternatingProdBlockHom a b
  let e := MonoidHom.ofInjective (alternatingProdBlockHom_injective a b)
  let r0 := (f.comp (alternatingBlockPreimage a b f).subtype).codRestrict
    i.range (fun x => x.2)
  calc
    (alternatingBlockPreimageProjection a b f).ker = r0.ker :=
      MonoidHom.ker_comp_of_injective r0 e.symm.toMonoidHom e.symm.injective
    _ = f.ker.comap (alternatingBlockPreimage a b f).subtype := by
      ext x
      dsimp [r0]
      constructor
      · intro hx
        have hx0 := MonoidHom.mem_ker.mp hx
        exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx0)
      · intro hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hx

public theorem alternatingBlockPreimageProjection_ker_le_center
    {H : Type*} [Group H] (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hker : f.ker ≤ Subgroup.center H) :
    (alternatingBlockPreimageProjection a b f).ker ≤
      Subgroup.center (alternatingBlockPreimage a b f) := by
  rw [alternatingBlockPreimageProjection_ker_eq_comap]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hx) y.1

/-- If a subgroup containing a Sylow `p`-subgroup splits over the restricted
global central `p`-kernel, then the global kernel is trivial.  This packages
the A1 33.11 Frattini contradiction used in block reductions. -/
public theorem kernel_eq_bot_of_sylow_le_subgroup_of_kernel_comap_isComplement'
    {H G : Type*} [Group H] [Finite H] [Group.IsPerfect H] [Group G]
    {p : Nat} [Fact p.Prime]
    (f : H →* G)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (P : Sylow p H)
    (E : Subgroup H) (hPE : (P : Subgroup H) ≤ E)
    (D : Subgroup E)
    (hcomp : (f.ker.comap E.subtype).IsComplement' D) :
    f.ker = ⊥ := by
  have hKleP : f.ker ≤ (P : Subgroup H) :=
    hkerp.le_sylow_of_normal P
  let i : P →* E :=
    (P : Subgroup H).subtype.codRestrict E (fun x => hPE x.2)
  let Kp : Subgroup P := f.ker.comap (P : Subgroup H).subtype
  let C : Subgroup P := D.comap i
  have hKpFrattini : Kp ≤ frattini P :=
    ker_comap_le_frattini_sylow P f hker
  have hsup : C ⊔ Kp = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨kd, hkd⟩ := hcomp.2 (i x)
    let k : f.ker.comap E.subtype := kd.1
    let d : D := kd.2
    have hkGlobal : ((k : E) : H) ∈ f.ker := k.2
    let kp : P := ⟨((k : E) : H), hKleP hkGlobal⟩
    have hkpKp : kp ∈ Kp := hkGlobal
    let dp : P := kp⁻¹ * x
    have hidp : i dp = d := by
      apply Subtype.ext
      change ((k : E) : H)⁻¹ * (x : H) = ((d : E) : H)
      have hkdH := congrArg (fun z : E => (z : H)) hkd
      change ((k : E) : H) * ((d : E) : H) = (x : H) at hkdH
      rw [← hkdH]
      simp
    have hdpC : dp ∈ C := by
      change i dp ∈ D
      rw [hidp]
      exact d.2
    have hkpSup : kp ∈ C ⊔ Kp := Subgroup.mem_sup_right hkpKp
    have hdpSup : dp ∈ C ⊔ Kp := Subgroup.mem_sup_left hdpC
    have hxSup := Subgroup.mul_mem (C ⊔ Kp) hkpSup hdpSup
    simpa [dp] using hxSup
  have hCfrattini : C ⊔ frattini P = ⊤ := by
    apply top_unique
    calc
      (⊤ : Subgroup P) = C ⊔ Kp := hsup.symm
      _ ≤ C ⊔ frattini P := sup_le_sup le_rfl hKpFrattini
  have hCtop : C = ⊤ :=
    frattini_nongenerating (K := C) hCfrattini
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  let zp : P := ⟨z, hKleP hz⟩
  have hzpC : zp ∈ C := by rw [hCtop]; trivial
  have hziD : i zp ∈ D := hzpC
  have hziK : i zp ∈ f.ker.comap E.subtype := hz
  have hdisj := hcomp.disjoint
  rw [Subgroup.disjoint_def] at hdisj
  have hziOne : i zp = 1 := hdisj hziK hziD
  exact congrArg (fun y : E => (y : H)) hziOne

public theorem exists_alternatingBlockPreimage_section_isComplement'
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker) :
    ∃ s : alternatingGroup (Fin (qA + 5)) ×
        alternatingGroup (Fin (qB + 5)) →*
        alternatingBlockPreimage (qA + 5) (qB + 5) f,
      (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f).comp s =
        MonoidHom.id _ ∧
      (alternatingBlockPreimageProjection (qA + 5) (qB + 5) f).ker.IsComplement'
        s.range := by
  let r := alternatingBlockPreimageProjection (qA + 5) (qB + 5) f
  have hrSurj : Function.Surjective r :=
    alternatingBlockPreimageProjection_surjective _ _ f hf
  have hrCenter : r.ker ≤
      Subgroup.center (alternatingBlockPreimage (qA + 5) (qB + 5) f) :=
    alternatingBlockPreimageProjection_ker_le_center _ _ f hker
  have hrP : IsPGroup p r.ker := by
    rw [alternatingBlockPreimageProjection_ker_eq_comap]
    exact hkerp.comap_subtype
  exact exists_prod_section_isComplement'_of_not_dvd_multipliers
    qA qB r hrSurj hrCenter hrP hpMA hpMB

/-- Block exclusion for the minimal-counterexample argument: if both block
factor multipliers have no `p`-part and the global central `p`-kernel is
nontrivial, no Sylow `p`-subgroup can lie in the two-block alternating
subgroup. -/
public theorem not_sylow_le_alternatingBlockPreimage_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime]
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker)
    (P : Sylow p H) :
    ¬ (P : Subgroup H) ≤
      alternatingBlockPreimage (qA + 5) (qB + 5) f := by
  intro hP
  obtain ⟨s, -, hcomp⟩ :=
    exists_alternatingBlockPreimage_section_isComplement'
      qA qB f hf hker hkerp hpMA hpMB
  have hkerEq : f.ker = ⊥ :=
    kernel_eq_bot_of_sylow_le_subgroup_of_kernel_comap_isComplement'
      f hker hkerp P
      (alternatingBlockPreimage (qA + 5) (qB + 5) f) hP s.range (by
        rw [← alternatingBlockPreimageProjection_ker_eq_comap]
        exact hcomp)
  rw [hkerEq, Subgroup.card_bot] at hpker
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hpker)

end GLS3.Chapter5.SchurPresentation
/- END Theory.BlockExtension -/

/- BEGIN Theory.PrimaryKernelQuotient -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5.SchurPresentation

/-- Cardinality of the image of a subgroup under a quotient, expressed as
the index of the induced kernel. -/
public theorem natCard_map_eq_index_of_subgroupOf_ker_eq'
    {H Q : Type*} [Group H] [Finite H] [Group Q]
    (K : Subgroup H) (U : Subgroup K) (q : H →* Q)
    (hker : q.ker.subgroupOf K = U) :
    Nat.card (K.map q) = U.index := by
  let r := q.subgroupMap K
  have hrker : r.ker = U := by
    rw [show r = q.subgroupMap K by rfl, Subgroup.ker_subgroupMap, hker]
  calc
    Nat.card (K.map q) = Nat.card r.range := by
      rw [MonoidHom.range_eq_top.mpr (q.subgroupMap_surjective K), Subgroup.card_top]
    _ = r.ker.index := (Subgroup.index_ker r).symm
    _ = U.index := by rw [hrker]

/-- A surjective homomorphism sends a central subgroup into the center. -/
public theorem map_le_center_of_le_center_of_surjective'
    {H Q : Type*} [Group H] [Group Q]
    (q : H →* Q) (hq : Function.Surjective q)
    {K : Subgroup H} (hK : K ≤ Subgroup.center H) :
    K.map q ≤ Subgroup.center Q := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨a, rfl⟩ := hq y
  rw [← map_mul, ← map_mul]
  exact congrArg q (Subgroup.mem_center_iff.mp (hK hx) a)

/-- Isolate a prescribed primary part of a central extension kernel.  If a
prime `p` divides the kernel of a finite perfect central extension, quotient
by a Schur--Zassenhaus complement to a Sylow `p`-subgroup of the kernel.  The
result is again a surjective central extension, now with a nontrivial
`p`-group kernel. -/
public theorem exists_pPrimary_quotient_central_extension
    {H G : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group G] [Finite G]
    {p : Nat} [Fact p.Prime]
    (f : H →* G) (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hpker : p ∣ Nat.card f.ker) :
    ∃ (X : Subgroup H) (_ : X.Normal)
      (fbar : (H ⧸ X) →* G),
      X ≤ f.ker ∧
      Function.Surjective fbar ∧
      fbar.ker ≤ Subgroup.center (H ⧸ X) ∧
      IsPGroup p fbar.ker ∧ p ∣ Nat.card fbar.ker := by
  let K := f.ker
  let : CommGroup (Subgroup.center H) := {
    mul_comm := fun a b => Subtype.ext
      (Subgroup.mem_center_iff.mp a.2 b.1).symm }
  let j : K →* Subgroup.center H :=
    K.subtype.codRestrict (Subgroup.center H) (fun x => hker x.2)
  let : CommGroup K := j.commGroupOfInjective (by
    intro a b hab
    dsimp [j] at hab
    apply Subtype.ext
    exact congrArg (fun z : Subgroup.center H => (z : H)) hab)
  let P : Sylow p K := default
  let : (P : Subgroup K).Normal := inferInstance
  obtain ⟨C, hPC⟩ :=
    Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  let X : Subgroup H := C.map K.subtype
  have hXker : X ≤ f.ker := by
    rintro x ⟨c, hc, rfl⟩
    exact c.2
  have hXcenter : X ≤ Subgroup.center H := hXker.trans hker
  let hXnormal : X.Normal := ⟨fun x hx a => by
    simpa [Subgroup.mem_center_iff.mp (hXcenter hx) a] using hx⟩
  let : X.Normal := hXnormal
  let q : H →* H ⧸ X := QuotientGroup.mk' X
  let fbar : (H ⧸ X) →* G := QuotientGroup.lift X f hXker
  have hqker : q.ker.subgroupOf K = C := by
    rw [show q = QuotientGroup.mk' X by rfl, QuotientGroup.ker_mk']
    change Subgroup.comap K.subtype (C.map K.subtype) = C
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective C
  have hfbarCard : Nat.card fbar.ker = Nat.card P := by
    rw [show fbar = QuotientGroup.lift X f hXker by rfl,
      QuotientGroup.ker_lift]
    exact (natCard_map_eq_index_of_subgroupOf_ker_eq' K C q hqker).trans
      hPC.index_eq_card
  have hfbarSurj : Function.Surjective fbar :=
    QuotientGroup.lift_surjective_of_surjective X f hsurj hXker
  have hfbarCenter : fbar.ker ≤ Subgroup.center (H ⧸ X) := by
    rw [show fbar = QuotientGroup.lift X f hXker by rfl,
      QuotientGroup.ker_lift]
    exact map_le_center_of_le_center_of_surjective' q
      (QuotientGroup.mk'_surjective X) hker
  have hfbarP : IsPGroup p fbar.ker := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    apply IsPGroup.of_card
    rw [hfbarCard, hk]
  have hpbar : p ∣ Nat.card fbar.ker := by
    rw [hfbarCard]
    exact P.dvd_card_of_dvd_card hpker
  exact ⟨X, hXnormal, fbar, hXker, hfbarSurj, hfbarCenter, hfbarP, hpbar⟩

end GLS3.Chapter5.SchurPresentation
/- END Theory.PrimaryKernelQuotient -/

/- BEGIN Theory.TwoRootFour -/
noncomputable section

/- Source: TwoRootFourLift.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

open scoped commutatorElement

open RootFourSubgroup

/-- A nontrivial finite perfect central extension of `A₅` has kernel of
cardinality two.  This packages such an extension as a covering and compares
it with the universal covering of `A₅`. -/
public theorem natCard_ker_eq_two_of_central_extension_alternatingGroup_five
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* alternatingGroup (Fin 5))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hne : f.ker ≠ ⊥) :
    Nat.card f.ker = 2 := by
  have hker_eq_center : f.ker = Subgroup.center H := by
    apply ker_eq_center_of_surjective_of_center_eq_bot f hsurj hker
    exact alternatingGroup.center_eq_bot (by simp)
  let e : H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq_center.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  let : IsQuasisimple H := {
    toIsPerfect := inferInstance
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
  }
  let c : Covering H (alternatingGroup (Fin 5)) := {
    toMonoidHom := f
    surjective := hsurj
  }
  have hdvd : Nat.card f.ker ∣ 2 := by
    have hdvd' := Covering.coveringKernel_card_dvd_of_universal
      (alternatingFreeCentralCovering 0)
      (alternatingFreeCentralCovering_isUniversal 0) c
    rw [natCard_ker_alternatingFreeCentralCovering_zero_eq_two] at hdvd'
    simpa [c] using hdvd'
  have hle : Nat.card f.ker ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have : Nonempty f.ker := ⟨1⟩
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hne_one : Nat.card f.ker ≠ 1 := by
    intro hcard
    apply hne
    exact Subgroup.card_eq_one.mp hcard
  omega

/-- In every nontrivial finite perfect central extension of `A₅`, the
standard root involution `rho1 0` has a lift whose square is nontrivial.  This
is the `A₅` base of the root-four square invariant in A1 33.15(2). -/
public theorem
    exists_lift_rho1_sq_ne_one_of_central_extension_alternatingGroup_five
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* alternatingGroup (Fin 5))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hne : f.ker ≠ ⊥) :
    ∃ u : H,
      f u = (⟨rho1 0, rho1_mem_alternating 0⟩ : alternatingGroup (Fin 5)) ∧
      u ^ 2 ≠ 1 := by
  have hcard : Nat.card f.ker = 2 :=
    natCard_ker_eq_two_of_central_extension_alternatingGroup_five
      f hsurj hker hne
  have hker_eq_center : f.ker = Subgroup.center H := by
    apply ker_eq_center_of_surjective_of_center_eq_bot f hsurj hker
    exact alternatingGroup.center_eq_bot (by simp)
  let e : H ⧸ Subgroup.center H ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq_center.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  let : IsQuasisimple H := {
    toIsPerfect := inferInstance
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact e.isSimpleGroup
  }
  let c : Covering H (alternatingGroup (Fin 5)) := {
    toMonoidHom := f
    surjective := hsurj
  }
  let a1 : alternatingGroup (Fin 5) :=
    ⟨rho1 0, rho1_mem_alternating 0⟩
  let a2 : alternatingGroup (Fin 5) :=
    ⟨rho2 0, rho2_mem_alternating 0⟩
  obtain ⟨u, hu⟩ := hsurj a1
  obtain ⟨v, hv⟩ := hsurj a2
  refine ⟨u, hu, ?_⟩
  let tauA : alternatingGroup (Fin 5) := schurAlternatingProjection 0 (g 0)
  obtain ⟨d, hd⟩ := hsurj tauA
  have hu' : f u = a1 := hu
  have hv' : f v = a2 := hv
  have hcomm : ⁅u, v⁆ ≠ 1 :=
    commutator_lifts_root_four_ne_one_of_card_ker_two
      f hsurj hker hcard u v hu' hv'
  have hu2ker : u ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, hu']
    apply Subtype.ext
    simpa [pow_two] using rho1_sq 0
  have hw2ker : (u * v) ^ 2 ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, map_mul, hu', hv']
    apply Subtype.ext
    simpa [a1, a2, pow_two, rho1_mul_rho2] using rho3_sq 0
  have hu2center : u ^ 2 ∈ Subgroup.center H := hker hu2ker
  have hw2center : (u * v) ^ 2 ∈ Subgroup.center H := hker hw2ker
  have hconj_u_image : f (d * u * d⁻¹) = f (u * v) := by
    rw [map_mul, map_mul, map_inv, hd, hu', map_mul, hu', hv']
    apply Subtype.ext
    change tau 0 * rho1 0 * (tau 0)⁻¹ = rho1 0 * rho2 0
    rw [tau_conj_rho1, rho1_mul_rho2]
  have hconj_w_image : f (d * (u * v) * d⁻¹) = f v := by
    rw [map_mul, map_mul, map_inv, hd, map_mul, hu', hv']
    apply Subtype.ext
    change tau 0 * (rho1 0 * rho2 0) * (tau 0)⁻¹ = rho2 0
    rw [rho1_mul_rho2]
    all_goals decide
  have hu2w2 : u ^ 2 = (u * v) ^ 2 := by
    calc
      u ^ 2 = (d * u * d⁻¹) ^ 2 := by
        rw [show (d * u * d⁻¹) ^ 2 = d * u ^ 2 * d⁻¹ by
          simp [pow_two, mul_assoc]]
        have hc := Subgroup.mem_center_iff.mp hu2center d
        rw [hc]
        simp
      _ = (u * v) ^ 2 :=
        DoubleCoverUniqueness.sq_eq_sq_of_apply_eq c hcard hconj_u_image
  have hw2v2 : (u * v) ^ 2 = v ^ 2 := by
    calc
      (u * v) ^ 2 = (d * (u * v) * d⁻¹) ^ 2 := by
        rw [show (d * (u * v) * d⁻¹) ^ 2 = d * (u * v) ^ 2 * d⁻¹ by
          simp [pow_two, mul_assoc]]
        have hc := Subgroup.mem_center_iff.mp hw2center d
        rw [hc]
        simp
      _ = v ^ 2 :=
        DoubleCoverUniqueness.sq_eq_sq_of_apply_eq c hcard hconj_w_image
  intro hu2one
  have huw2one : (u * v) ^ 2 = 1 := by rw [← hu2w2, hu2one]
  have hv2one : v ^ 2 = 1 := by rw [← hw2v2, huw2one]
  have hu_inv : u = u⁻¹ :=
    mul_eq_one_iff_eq_inv.mp (by simpa [pow_two] using hu2one)
  have hv_inv : v = v⁻¹ :=
    mul_eq_one_iff_eq_inv.mp (by simpa [pow_two] using hv2one)
  have huw_inv : u * v = (u * v)⁻¹ :=
    mul_eq_one_iff_eq_inv.mp (by simpa [pow_two] using huw2one)
  apply hcomm
  rw [commutatorElement_eq_one_iff_mul_comm]
  calc
    u * v = (u * v)⁻¹ := huw_inv
    _ = v⁻¹ * u⁻¹ := by rw [mul_inv_rev]
    _ = v * u := by rw [← hu_inv, ← hv_inv]

end GLS3.Chapter5.SchurPresentation

/- Source: TwoRootFourTransfer.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

open RootFourSubgroup

/-- If the universal kernel for `A_(q+5)` has cardinality at most two, then
every finite perfect central extension has the same cardinal bound and admits
a lift of the standard root involution whose square generates its kernel.  The
trivial-kernel and double-cover cases are handled uniformly in the conclusion.
-/
public theorem
    natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
    (q : Nat)
    (hM : Nat.card (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (f : H →* alternatingGroup (Fin (q + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H) :
    Nat.card f.ker ≤ 2 ∧
      ∃ u : H,
        f u = (⟨rho1 q, rho1_mem_alternating q⟩ :
          alternatingGroup (Fin (q + 5))) ∧
        f.ker = Subgroup.zpowers (u ^ 2) := by
  have hM2 : Nat.card (alternatingFreeCentralCovering q).toMonoidHom.ker = 2 :=
    Nat.le_antisymm hM
      (two_le_natCard_ker_alternatingFreeCentralCovering q)
  have hker_eq_center : f.ker = Subgroup.center H := by
    apply ker_eq_center_of_surjective_of_center_eq_bot f hsurj hker
    exact alternatingGroup.center_eq_bot (by simp)
  let eH : H ⧸ Subgroup.center H ≃* alternatingGroup (Fin (q + 5)) :=
    (QuotientGroup.quotientMulEquivOfEq hker_eq_center.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
  let : IsQuasisimple H := {
    toIsPerfect := inferInstance
    simple := by
      let : IsSimpleGroup (alternatingGroup (Fin (q + 5))) :=
        alternatingGroup.isSimpleGroup (by simp)
      exact eH.isSimpleGroup
  }
  let c : Covering H (alternatingGroup (Fin (q + 5))) := {
    toMonoidHom := f
    surjective := hsurj
  }
  let a1 : alternatingGroup (Fin (q + 5)) :=
    ⟨rho1 q, rho1_mem_alternating q⟩
  rcases Covering.coveringKernel_card_eq_one_or_two
      (alternatingFreeCentralCovering q)
      (alternatingFreeCentralCovering_isUniversal q) hM2 c with hcard | hcard
  · have hcardf : Nat.card f.ker = 1 := by simpa [c] using hcard
    refine ⟨by omega, ?_⟩
    obtain ⟨u, hu⟩ := hsurj a1
    have hu2ker : u ^ 2 ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, hu]
      apply Subtype.ext
      simpa [pow_two] using rho1_sq q
    have hbot : f.ker = ⊥ := Subgroup.card_eq_one.mp hcardf
    have hu2one : u ^ 2 = 1 := by
      have hu2bot : u ^ 2 ∈ (⊥ : Subgroup H) := by
        rw [← hbot]
        exact hu2ker
      exact Subgroup.mem_bot.mp hu2bot
    refine ⟨u, hu, ?_⟩
    simp [hbot, hu2one]
  · have hcardf : Nat.card f.ker = 2 := by simpa [c] using hcard
    refine ⟨by omega, ?_⟩
    obtain ⟨e, he, _⟩ := Covering.coveringIso_of_card_two
      (alternatingFreeCentralCovering q)
      (alternatingFreeCentralCovering_isUniversal q)
      (alternatingFreeCentralCovering_isUniversal q) hM2
      (schurAlternatingCovering q) c
      (natCard_ker_schurAlternatingCovering q) hcard
    let u : H := e (u1 q)
    have hstd : schurAlternatingCovering q (u1 q) = a1 := by
      apply Subtype.ext
      exact u1_proj q
    have hfac : c (e (u1 q)) = schurAlternatingCovering q (u1 q) := by
      change (c.comp (Covering.ofMulEquiv e)) (u1 q) =
        schurAlternatingCovering q (u1 q)
      rw [he]
    have hu : f u = a1 := by
      change c (e (u1 q)) = a1
      exact hfac.trans hstd
    have hu2ne : u ^ 2 ≠ 1 := by
      have hu2eq : u ^ 2 = e (schurAlternatingCentral q) := by
        change e (u1 q) ^ 2 = e (schurAlternatingCentral q)
        rw [← map_pow, u1_sq]
      rw [hu2eq]
      intro h
      apply schurAlternatingCentral_ne_one q
      apply e.injective
      simpa using h
    have hu2ker : u ^ 2 ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_pow, hu]
      apply Subtype.ext
      simpa [pow_two] using rho1_sq q
    have hzle : Subgroup.zpowers (u ^ 2) ≤ f.ker :=
      Subgroup.zpowers_le.mpr hu2ker
    have hz_ne_bot : Subgroup.zpowers (u ^ 2) ≠ ⊥ :=
      Subgroup.zpowers_ne_bot.mpr hu2ne
    let : Nontrivial (Subgroup.zpowers (u ^ 2)) :=
      (Subgroup.nontrivial_iff_ne_bot (Subgroup.zpowers (u ^ 2))).mpr hz_ne_bot
    have hzcard : 2 ≤ Nat.card (Subgroup.zpowers (u ^ 2)) := by
      have hgt : 1 < Nat.card (Subgroup.zpowers (u ^ 2)) :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      omega
    have heq : Subgroup.zpowers (u ^ 2) = f.ker :=
      Subgroup.eq_of_le_of_card_ge hzle (by rw [hcardf]; exact hzcard)
    exact ⟨u, hu, heq.symm⟩

/-- In a central extension with kernel cardinality at most two, lifts of the
same base element have equal squares. -/
public theorem sq_eq_sq_of_apply_eq_of_card_ker_le_two
    {H G : Type*} [Group H] [Finite H] [Group G]
    (f : H →* G) (hker : f.ker ≤ Subgroup.center H)
    (hcard : Nat.card f.ker ≤ 2)
    {x y : H} (hxy : f x = f y) :
    x ^ 2 = y ^ 2 := by
  let k := x * y⁻¹
  have hk : k ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy]
    simp
  have hk2 : k ^ 2 = 1 := by
    have hpow := pow_card_eq_one' (x := (⟨k, hk⟩ : f.ker))
    have : Nonempty f.ker := ⟨1⟩
    have hpos : 0 < Nat.card f.ker := Nat.card_pos
    have hcases : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 := by omega
    rcases hcases with hcard1 | hcard2
    · rw [hcard1] at hpow
      have hkone : k = 1 := by
        simpa using congrArg Subtype.val hpow
      simp [hkone]
    · rw [hcard2] at hpow
      simpa using congrArg Subtype.val hpow
  have hkcenter : k ∈ Subgroup.center H := hker hk
  have hcomm : Commute k y :=
    (Subgroup.mem_center_iff.mp hkcenter y).symm
  have hxy' : x = k * y := by simp [k]
  calc
    x ^ 2 = (k * y) ^ 2 := by rw [hxy']
    _ = k ^ 2 * y ^ 2 := hcomm.mul_pow 2
    _ = y ^ 2 := by rw [hk2]; simp

/-- Derived-subgroup form of the paired transfer theorem.  It applies to a
central extension whose ambient group need not itself be perfect. -/
public theorem
    derived_natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
    (q : Nat)
    (hM : Nat.card (alternatingFreeCentralCovering q).toMonoidHom.ker ≤ 2)
    {E : Type} [Group E] [Finite E]
    (r : E →* alternatingGroup (Fin (q + 5)))
    (hr : Function.Surjective r)
    (hker : r.ker ≤ Subgroup.center E) :
    Nat.card (r.comp (commutator E).subtype).ker ≤ 2 ∧
      ∃ u : commutator E,
        (r.comp (commutator E).subtype) u =
          (⟨rho1 q, rho1_mem_alternating q⟩ :
            alternatingGroup (Fin (q + 5))) ∧
        (r.comp (commutator E).subtype).ker =
          Subgroup.zpowers (u ^ 2) := by
  let D := commutator E
  let rD := r.comp D.subtype
  let : Group.IsPerfect D :=
    commutator_isPerfect_of_surjective_of_ker_le_center r hr hker
  let : Finite D := inferInstance
  have hrDsurj : Function.Surjective rD := by
    have hmap : D.map r = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hr]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ D.map r := by rw [hmap]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have hrDcenter : rD.ker ≤ Subgroup.center D := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker hx) y
  exact
    natCard_ker_le_two_and_exists_lift_rho1_ker_eq_zpowers_of_multiplier_le_two
      q hM rD hrDsurj hrDcenter

end GLS3.Chapter5.SchurPresentation
/- END Theory.TwoRootFour -/

/- BEGIN Theory.AlternatingCentralizerSignKernelValue -/
noncomputable section

namespace GLS3.Chapter5

public theorem alternatingCentralizerSignKernelEquivFixedConjNormal_coe
    {n : Nat} (σ : Equiv.Perm (Fin n))
    (z : (Equiv.Perm.sign.comp
      (Subgroup.subtype (Subgroup.centralizer
        ({σ} : Set (Equiv.Perm (Fin n)))))).ker) :
    ((alternatingCentralizerSignKernelEquivFixedConjNormal σ) z).1.1 =
      z.1.1 := by
  rfl

end GLS3.Chapter5
/- END Theory.AlternatingCentralizerSignKernelValue -/

/- BEGIN Theory.SignKernelDecompositionRotationOddPair -/
noncomputable section

namespace GLS3.Chapter5

private theorem __ch5_SignKernelDecompositionRotationOddPair_intUnits_eq_of_mul_eq_one {u v : ℤˣ}
    (huv : u * v = 1) : u = v := by
  rcases Int.units_eq_one_or u with hu | hu <;>
    rcases Int.units_eq_one_or v with hv | hv
  · exact hu.trans hv.symm
  · rw [hu, hv] at huv
    norm_num at huv
  · rw [hu, hv] at huv
    norm_num at huv
  · exact hu.trans hv.symm

/-- Suppose a group is the product of a rotation-complement factor `R ⋊ L`
and a commuting factor `I`, with `L` entirely in a sign kernel. If `R` and
`I` contain odd involutions, then their product adjoins the missing coset to
the kernel factors. -/
public theorem signKernel_decomp_rotation_odd_pair
    {C : Type*} [Group C] (χ : C →* ℤˣ)
    (R L I : Subgroup C)
    (hLχ : L ≤ χ.ker)
    (hLnorm : L ≤ Subgroup.normalizer R)
    (hIcomm : I ≤ Subgroup.centralizer
      ((R ⊔ L : Subgroup C) : Set C))
    (hsup : I ⊔ (R ⊔ L) = ⊤)
    (r0 i0 : C) (hr0 : r0 ∈ R) (hi0 : i0 ∈ I)
    (hr0χ : χ r0 = -1) (hi0χ : χ i0 = -1)
    (hr02 : r0 ^ 2 = 1) (hi02 : i0 ^ 2 = 1) :
    let Z := χ.ker
    let RZ := R.comap Z.subtype
    let LZ := L.comap Z.subtype
    let IZ := I.comap Z.subtype
    let t : Z := ⟨i0 * r0, by
      rw [MonoidHom.mem_ker, map_mul, hi0χ, hr0χ]
      norm_num⟩
    ((RZ ⊔ LZ) ⊔ IZ) ⊔ Subgroup.zpowers t = ⊤ ∧ t ^ 2 = 1 := by
  dsimp only
  let t : χ.ker := ⟨i0 * r0, by
    rw [MonoidHom.mem_ker, map_mul, hi0χ, hr0χ]
    norm_num⟩
  have hi0r0 : Commute i0 r0 := by
    have himem := hIcomm hi0
    rw [Subgroup.mem_centralizer_iff] at himem
    exact (himem r0 ((le_sup_left : R ≤ R ⊔ L) hr0)).symm
  have ht2 : t ^ 2 = 1 := by
    apply Subtype.ext
    change (i0 * r0) ^ 2 = 1
    rw [pow_two]
    calc
      i0 * r0 * (i0 * r0) = i0 * (r0 * i0) * r0 := by group
      _ = i0 * (i0 * r0) * r0 := by rw [hi0r0.eq]
      _ = (i0 ^ 2) * (r0 ^ 2) := by simp [pow_two, mul_assoc]
      _ = 1 := by rw [hi02, hr02, one_mul]
  constructor
  · apply top_unique
    intro z _
    have hz : z.1 ∈ I ⊔ (R ⊔ L) := by rw [hsup]; trivial
    have hRLnormI : R ⊔ L ≤ Subgroup.normalizer I :=
      (Subgroup.le_centralizer_iff.mp hIcomm).trans
        (Subgroup.centralizer_le_normalizer (I : Set C))
    change z.1 ∈ (↑(I ⊔ (R ⊔ L)) : Set C) at hz
    rw [Subgroup.coe_mul_of_right_le_normalizer_left I (R ⊔ L) hRLnormI] at hz
    rcases hz with ⟨i, hi, w, hw, hiw⟩
    change w ∈ (↑(R ⊔ L) : Set C) at hw
    rw [Subgroup.coe_mul_of_right_le_normalizer_left R L hLnorm] at hw
    rcases hw with ⟨r, hr, l, hl, hrl⟩
    let r' : C := l⁻¹ * r * l
    have hr' : r' ∈ R := by
      have hnorm := hLnorm (L.inv_mem hl)
      rw [Subgroup.mem_normalizer_iff] at hnorm
      dsimp [r']
      simpa only [inv_inv] using (hnorm r).mp hr
    have hrl' : r * l = l * r' := by
      dsimp [r']
      group
    have hzval : z.1 = i * (l * r') :=
      hiw.symm.trans (congrArg (i * ·) (hrl.symm.trans hrl'))
    have hlχ : χ l = 1 := MonoidHom.mem_ker.mp (hLχ hl)
    have hr'χ : χ r' = χ r := by simp [r', hlχ]
    have hzχ : χ z.1 = 1 := MonoidHom.mem_ker.mp z.2
    rw [hzval, map_mul, map_mul, hlχ, one_mul] at hzχ
    have hir : χ i = χ r' := __ch5_SignKernelDecompositionRotationOddPair_intUnits_eq_of_mul_eq_one hzχ
    rcases Int.units_eq_one_or (χ i) with hiχ | hiχ
    · have hrχ : χ r' = 1 := hir.symm.trans hiχ
      let iz : χ.ker := ⟨i, MonoidHom.mem_ker.mpr hiχ⟩
      let rz : χ.ker := ⟨r', MonoidHom.mem_ker.mpr hrχ⟩
      let lz : χ.ker := ⟨l, hLχ hl⟩
      have hbase : iz * (lz * rz) ∈
          (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype := by
        apply Subgroup.mul_mem
        · exact (le_sup_right : I.comap (χ.ker).subtype ≤
            (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
              I.comap (χ.ker).subtype) hi
        · exact (le_sup_left :
            R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype ≤
              (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
                I.comap (χ.ker).subtype)
            ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype).mul_mem
              ((le_sup_right : L.comap (χ.ker).subtype ≤
                R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hl)
              ((le_sup_left : R.comap (χ.ker).subtype ≤
                R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hr'))
      have heq : z = iz * (lz * rz) := Subtype.ext hzval
      rw [heq]
      exact (le_sup_left :
        (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
          I.comap (χ.ker).subtype ≤
        ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
          I.comap (χ.ker).subtype) ⊔ Subgroup.zpowers t) hbase
    · have hrχ : χ r' = -1 := hir.symm.trans hiχ
      have hii0χ : χ (i * i0) = 1 := by simp [hiχ, hi0χ]
      have hrr0χ : χ (r' * r0) = 1 := by simp [hrχ, hr0χ]
      let iz : χ.ker := ⟨i * i0, MonoidHom.mem_ker.mpr hii0χ⟩
      let rz : χ.ker := ⟨r' * r0, MonoidHom.mem_ker.mpr hrr0χ⟩
      let lz : χ.ker := ⟨l, hLχ hl⟩
      have hi0lr : Commute i0 (l * (r' * r0)) := by
        have himem := hIcomm hi0
        rw [Subgroup.mem_centralizer_iff] at himem
        exact (himem _ ((R ⊔ L).mul_mem
          ((le_sup_right : L ≤ R ⊔ L) hl)
          ((R ⊔ L).mul_mem
            ((le_sup_left : R ≤ R ⊔ L) hr')
            ((le_sup_left : R ≤ R ⊔ L) hr0)))).symm
      have hbase : iz * (lz * rz) ∈
          (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype := by
        apply Subgroup.mul_mem
        · exact (le_sup_right : I.comap (χ.ker).subtype ≤
            (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
              I.comap (χ.ker).subtype) (I.mul_mem hi hi0)
        · exact (le_sup_left :
            R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype ≤
              (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
                I.comap (χ.ker).subtype)
            ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype).mul_mem
              ((le_sup_right : L.comap (χ.ker).subtype ≤
                R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hl)
              ((le_sup_left : R.comap (χ.ker).subtype ≤
                R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype)
                (R.mul_mem hr' hr0)))
      have htmem : t ∈ Subgroup.zpowers t := Subgroup.mem_zpowers t
      have heq : z = (iz * (lz * rz)) * t := by
        apply Subtype.ext
        change z.1 = ((i * i0) * (l * (r' * r0))) * (i0 * r0)
        refine hzval.trans ?_
        symm
        calc
          ((i * i0) * (l * (r' * r0))) * (i0 * r0) =
              i * (i0 * (l * (r' * r0))) * i0 * r0 := by group
          _ = i * ((l * (r' * r0)) * i0) * i0 * r0 := by rw [hi0lr.eq]
          _ = i * (l * (r' * r0)) * (i0 ^ 2) * r0 := by
            simp [pow_two, mul_assoc]
          _ = i * (l * (r' * r0)) * r0 := by rw [hi02]; simp
          _ = i * (l * r') * (r0 ^ 2) := by simp [pow_two, mul_assoc]
          _ = i * (l * r') := by rw [hr02]; simp
      rw [heq]
      exact Subgroup.mul_mem _
        ((le_sup_left :
          (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype ≤
          ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype) ⊔ Subgroup.zpowers t) hbase)
        ((le_sup_right : Subgroup.zpowers t ≤
          ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype) ⊔ Subgroup.zpowers t) htmem)
  · exact ht2

end GLS3.Chapter5
/- END Theory.SignKernelDecompositionRotationOddPair -/

/- BEGIN Theory.SubgroupComapKernelEquivOfLe -/
noncomputable section

namespace GLS3.Chapter5

/-- A subgroup already contained in a homomorphism kernel is canonically
isomorphic to its pullback inside that kernel. -/
@[expose]
public noncomputable def subgroupComapKernelEquivOfLe
    {C M : Type*} [Group C] [Group M]
    (χ : C →* M) (H : Subgroup C) (hH : H ≤ χ.ker) :
    H.comap χ.ker.subtype ≃* H where
  toFun z := ⟨z.1.1, z.2⟩
  invFun h := ⟨⟨h.1, hH h.2⟩, h.2⟩
  left_inv z := by ext; rfl
  right_inv h := by ext; rfl
  map_mul' _ _ := rfl

@[simp]
public theorem subgroupComapKernelEquivOfLe_apply_coe
    {C M : Type*} [Group C] [Group M]
    (χ : C →* M) (H : Subgroup C) (hH : H ≤ χ.ker)
    (z : H.comap χ.ker.subtype) :
    ((subgroupComapKernelEquivOfLe χ H hH z : H) : C) = z.1.1 := rfl

end GLS3.Chapter5
/- END Theory.SubgroupComapKernelEquivOfLe -/

/- BEGIN Theory.InvolutionRemainderDisjointCycleSwap -/
noncomputable section
namespace GLS3.Chapter5
universe __ch5_InvolutionRemainderDisjointCycleSwap_u

public theorem involutionRemainder_disjoint_cycleSwap
    {Ω : Type __ch5_InvolutionRemainderDisjointCycleSwap_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (c d : x.cycleFactorsFinset) (hcd : c ≠ d) :
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    let l := e.symm (Equiv.swap c d)
    let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
      fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
    let a := (involutionCycleRotationCoordinates x hx).symm v
    Equiv.Perm.Disjoint l.1.1 (x * (cycleRotationToCentralizer x a).1) := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  let l := e.symm (Equiv.swap c d)
  let E := involutionCycleRotationCoordinates x hx
  let v : x.cycleFactorsFinset → Multiplicative (ZMod 2) :=
    fun k => if k = c ∨ k = d then Multiplicative.ofAdd 1 else 1
  let a := E.symm v
  let ρ := (cycleRotationToCentralizer x a).1
  have haCoord : E a = v := E.apply_symm_apply v
  have hac : a c = cycleFactorGenerator c := by
    let ec := zmodMulEquivOfGenerator (cycleFactorGenerator_generates c)
      (by simpa [hx] using cycleFactorZPowers_card_of_primeOrder x hp c)
    apply ec.symm.injective
    have hcCoord := congrFun haCoord c
    change ec.symm (a c) = v c at hcCoord
    calc
      ec.symm (a c) = Multiplicative.ofAdd 1 := by simpa [v] using hcCoord
      _ = ec.symm (cycleFactorGenerator c) :=
        (zmodMulEquivOfGenerator_symm_apply_generator
          (cycleFactorGenerator_generates c)
          (by simpa [hx] using cycleFactorZPowers_card_of_primeOrder x hp c)).symm
  have had : a d = cycleFactorGenerator d := by
    let ed := zmodMulEquivOfGenerator (cycleFactorGenerator_generates d)
      (by simpa [hx] using cycleFactorZPowers_card_of_primeOrder x hp d)
    apply ed.symm.injective
    have hdCoord := congrFun haCoord d
    change ed.symm (a d) = v d at hdCoord
    calc
      ed.symm (a d) = Multiplicative.ofAdd 1 := by simpa [v, hcd] using hdCoord
      _ = ed.symm (cycleFactorGenerator d) :=
        (zmodMulEquivOfGenerator_symm_apply_generator
          (cycleFactorGenerator_generates d)
          (by simpa [hx] using cycleFactorZPowers_card_of_primeOrder x hp d)).symm
  rw [Equiv.Perm.disjoint_iff_disjoint_support]
  rw [show l.1.1.support = c.1.support ∪ d.1.support by
    simpa [e, l] using involutionCycleSwap_support_eq_union x hx c d hcd]
  rw [Finset.disjoint_left]
  intro ω hω hprod
  rw [Equiv.Perm.mem_support] at hprod
  apply hprod
  rcases Finset.mem_union.mp hω with hωc | hωd
  · obtain ⟨n, hn⟩ := (cycleCoordinateEquiv x hp c).surjective ⟨ω, hωc⟩
    have hnval := congrArg Subtype.val hn
    change (x * ρ) ω = ω
    calc
      (x * ρ) ω = (x * ρ) (cycleCoordinateEquiv x hp c n).1 :=
        congrArg (x * ρ) hnval.symm
      _ = (cycleCoordinateEquiv x hp c n).1 := by
        change x ((cycleRotationToCentralizer x a).1
          (cycleCoordinateEquiv x hp c n).1) = _
        rw [cycleRotationToCentralizer_apply_cycleCoordinate x hp a c n, hac]
        change x (c.1 (cycleCoordinateEquiv x hp c n).1) = _
        rw [← cycleCoordinateEquiv_add_one x hp c n,
          x_apply_cycleCoordinateEquiv x hp c]
        rw [show n + 1 + 1 = n by
          apply (ZMod.ringEquivCongr hx).injective
          simp only [map_add, map_one]
          rw [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]]
      _ = ω := hnval
  · obtain ⟨n, hn⟩ := (cycleCoordinateEquiv x hp d).surjective ⟨ω, hωd⟩
    have hnval := congrArg Subtype.val hn
    change (x * ρ) ω = ω
    calc
      (x * ρ) ω = (x * ρ) (cycleCoordinateEquiv x hp d n).1 :=
        congrArg (x * ρ) hnval.symm
      _ = (cycleCoordinateEquiv x hp d n).1 := by
        change x ((cycleRotationToCentralizer x a).1
          (cycleCoordinateEquiv x hp d n).1) = _
        rw [cycleRotationToCentralizer_apply_cycleCoordinate x hp a d n, had]
        change x (d.1 (cycleCoordinateEquiv x hp d n).1) = _
        rw [← cycleCoordinateEquiv_add_one x hp d n,
          x_apply_cycleCoordinateEquiv x hp d]
        rw [show n + 1 + 1 = n by
          apply (ZMod.ringEquivCongr hx).injective
          simp only [map_add, map_one]
          rw [add_assoc, show (1 : ZMod 2) + 1 = 0 by decide, add_zero]]
      _ = ω := hnval

end GLS3.Chapter5
/- END Theory.InvolutionRemainderDisjointCycleSwap -/

/- BEGIN Theory.SemidirectExtension -/
universe __ch5_SemidirectExtension_u __ch5_SemidirectExtension_v __ch5_SemidirectExtension_w

noncomputable section

/- Source: SemidirectProductExtension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

open scoped Pointwise

/-! ## Central extensions of semidirect products

If a central extension of `N semidirectProduct A` splits over both canonical
factors and `N` is perfect, the two factor sections automatically satisfy the
semidirect compatibility relation.  Indeed, conjugating the `N`-section by an
`A`-lift and first applying the prescribed action give two lifts of the same
map from the perfect group `N`; central-lift uniqueness makes them equal.
-/


/-- A central subgroup admitting a complement in a perfect group is trivial.
The complement gives a homomorphic projection onto the central factor, while
perfectness kills every homomorphism to that abelian factor. -/
public theorem central_subgroup_eq_bot_of_isPerfect_of_isComplement'
    {H : Type __ch5_SemidirectExtension_u} [Group H] [Group.IsPerfect H]
    (X Y : Subgroup H) (hX : X ≤ Subgroup.center H)
    (hXY : X.IsComplement' Y) : X = ⊥ := by
  let : CommGroup X := {
    mul_comm := fun x y => Subtype.ext
      (Subgroup.mem_center_iff.mp (hX x.2) y.1).symm }
  let r : H →* X := centralComplementProjection X Y hXY hX
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  let xX : X := ⟨x, hx⟩
  have hrx : r x = xX :=
    centralComplementProjection_apply_left X Y hXY hX xX
  have hrone : r x = 1 := by
    apply MonoidHom.mem_ker.mp
    exact Abelianization.commutator_subset_ker r
      (Group.IsPerfect.mem_commutator (g := x))
  exact congrArg Subtype.val (hrx.symm.trans hrone)

set_option backward.isDefEq.respectTransparency false in
/-- Component sections of a central extension of a semidirect product combine
to a section of the whole semidirect product when the normal factor is
perfect.  The section image is a complement to the central kernel. -/
public theorem
    exists_semidirectProduct_section_isComplement'_of_component_sections
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A] [Group.IsPerfect N]
    (φ : A →* MulAut N)
    (f : H →* N ⋊[φ] A)
    (hker : f.ker ≤ Subgroup.center H)
    (sN : N →* H) (sA : A →* H)
    (hsN : f.comp sN = SemidirectProduct.inl)
    (hsA : f.comp sA = SemidirectProduct.inr) :
    ∃ s : N ⋊[φ] A →* H,
      f.comp s = MonoidHom.id _ ∧ f.ker.IsComplement' s.range := by
  have hsN_apply (n : N) : f (sN n) = SemidirectProduct.inl n :=
    DFunLike.congr_fun hsN n
  have hsA_apply (a : A) : f (sA a) = SemidirectProduct.inr a :=
    DFunLike.congr_fun hsA a
  have hcompat (a : A) :
      sN.comp (φ a).toMonoidHom =
        (MulAut.conj (sA a)).toMonoidHom.comp sN := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq f hker
    apply MonoidHom.ext
    intro n
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, map_mul, map_inv, hsN_apply, hsA_apply]
    simpa only [map_inv] using (SemidirectProduct.inl_aut (φ := φ) a n)
  let s : N ⋊[φ] A →* H := SemidirectProduct.lift sN sA hcompat
  have hsec : f.comp s = MonoidHom.id (N ⋊[φ] A) := by
    apply SemidirectProduct.hom_ext
    · rw [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inl, hsN]
      rfl
    · rw [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inr, hsA]
      rfl
  have hdisj : Disjoint f.ker s.range := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    obtain ⟨y, rfl⟩ := hxR
    have hy : y = 1 := by
      have hxy : f (s y) = y := DFunLike.congr_fun hsec y
      have hfone : f (s y) = 1 := MonoidHom.mem_ker.mp hxK
      exact hxy.symm.trans hfone
    rw [hy]
    exact map_one s
  have hmul : (f.ker : Set H) * (s.range : Set H) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    let y := s (f x)
    let k := x * y⁻¹
    have hyf : f y = f x := by
      have hxy : f (s (f x)) = f x := DFunLike.congr_fun hsec (f x)
      exact hxy
    have hk : k ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [k]
      rw [map_mul, map_inv, hyf]
      simp
    have hy : y ∈ s.range := ⟨f x, rfl⟩
    apply Set.mem_mul.mpr
    exact ⟨k, hk, y, hy, by simp [k]⟩
  exact ⟨s, hsec,
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul⟩

end GLS3.Chapter5.SchurPresentation

/- Source: DirectPowerExtension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

open scoped Pointwise

/-! ## Central extensions of finite direct powers

The direct-product splitting argument can be iterated over a finite power of
one alternating group.  If the extension group is perfect, a resulting
central complement would be an abelian quotient of a perfect group and hence
must be trivial.
-/


/-- Split a function on `Fin (n + 1)` into its zeroth coordinate and its tail,
as a group isomorphism. -/
public def finSuccArrowMulEquiv (A : Type __ch5_SemidirectExtension_v) [Group A] (n : Nat) :
    (Fin (n + 1) → A) ≃* A × (Fin n → A) where
  toFun x := (x 0, fun i => x i.succ)
  invFun x := Fin.cases x.1 x.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      rfl
  map_mul' x y := rfl

/-- Evaluation at the unique coordinate identifies a one-fold power with its
factor. -/
public def finOneArrowMulEquiv (A : Type __ch5_SemidirectExtension_v) [Group A] : (Fin 1 → A) ≃* A where
  toFun x := x 0
  invFun a := fun _ => a
  left_inv x := by
    funext i
    exact congrArg x (Subsingleton.elim 0 i)
  right_inv x := rfl
  map_mul' x y := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The alternating left component of a central extension of `A × B` has
trivial derived kernel whenever the global kernel is p-primary and the
alternating multiplier has no p-part.  The right factor is arbitrary. -/
public theorem
    prodLeftPreimageDerivedProjection_ker_eq_bot_of_not_dvd_multiplier_of_arbitrary_right
    {H B : Type} [Group H] [Finite H] [Group B]
    {p : Nat} [Fact p.Prime]
    (q : Nat)
    (f : H →* alternatingGroup (Fin (q + 5)) × B)
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker) :
    (prodLeftPreimageDerivedProjection f).ker = ⊥ := by
  have hkerpE : IsPGroup p
      (f.ker.comap (prodLeftPreimage f).subtype) :=
    hkerp.comap_subtype
  have hkerpD : IsPGroup p
      (prodLeftPreimageDerivedProjection f).ker := by
    rw [prodLeftPreimageDerivedProjection_ker_eq_comap,
      prodLeftPreimageProjection_ker_eq_comap]
    exact hkerpE.comap_subtype
  have hdvd0 :=
    alternatingCentralExtensionDerived_ker_card_dvd_multiplier q
      (prodLeftPreimageProjection f)
      (prodLeftPreimageProjection_surjective f hf)
      (prodLeftPreimageProjection_ker_le_center f hker)
  rw [show ((prodLeftPreimageProjection f).comp
      (commutator (prodLeftPreimage f)).subtype).ker =
      (prodLeftPreimageProjection f).ker.comap
        (commutator (prodLeftPreimage f)).subtype by rfl] at hdvd0
  rw [← prodLeftPreimageDerivedProjection_ker_eq_comap] at hdvd0
  have hdvd : Nat.card (prodLeftPreimageDerivedProjection f).ker ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker := hdvd0
  have hcard : Nat.card (prodLeftPreimageDerivedProjection f).ker = 1 := by
    rcases hkerpD.card_eq_or_dvd with h1 | hp
    · exact h1
    · exact False.elim (hpM (hp.trans hdvd))
  exact Subgroup.card_eq_one.mp hcard

set_option backward.isDefEq.respectTransparency false in
/-- A perfect finite central extension of a finite direct power of
`A_{q+5}` has trivial p-primary kernel if p does not divide the multiplier of
one factor. -/
public theorem directPowerCentralExtension_ker_eq_bot_of_not_dvd_multiplier
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime]
    (q n : Nat)
    (f : H →* (Fin n → alternatingGroup (Fin (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker) :
    f.ker = ⊥ := by
  induction n generalizing H with
  | zero =>
      let : IsMulCommutative H :=
        ⟨⟨fun x y => by
          have hx : x ∈ f.ker := by
            rw [MonoidHom.mem_ker]
            exact Subsingleton.elim _ _
          exact (Subgroup.mem_center_iff.mp (hker hx) y).symm⟩⟩
      let : Subsingleton H := inferInstance
      rw [Subgroup.eq_bot_iff_forall]
      intro x _
      exact Subsingleton.elim x 1
  | succ n ih =>
      let A := alternatingGroup (Fin (q + 5))
      let e : (Fin (n + 1) → A) ≃* A × (Fin n → A) :=
        finSuccArrowMulEquiv A n
      let f' : H →* A × (Fin n → A) := e.toMonoidHom.comp f
      have hf' : Function.Surjective f' := e.surjective.comp hf
      have hker_eq : f'.ker = f.ker := by
        ext x
        change e (f x) = 1 ↔ f x = 1
        constructor
        · intro hx
          apply e.injective
          simpa using hx
        · intro hx
          simp [hx]
      have hker' : f'.ker ≤ Subgroup.center H := by
        rw [hker_eq]
        exact hker
      have hkerp' : IsPGroup p f'.ker := by
        rw [hker_eq]
        exact hkerp
      have hleft : (prodLeftPreimageDerivedProjection f').ker = ⊥ :=
        prodLeftPreimageDerivedProjection_ker_eq_bot_of_not_dvd_multiplier_of_arbitrary_right
          q f' hf' hker' hkerp' hpM
      let DR := prodRightPreimageDerived f'
      let rR := prodRightPreimageDerivedProjection f'
      let : Group.IsPerfect A :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      let : Group.IsPerfect (Fin n → A) := {
        commutator_eq_top := by
          change ⁅(⊤ : Subgroup (Fin n → A)), ⊤⁆ = ⊤
          rw [← Subgroup.pi_top (f := fun _ : Fin n => A) Set.univ]
          rw [Subgroup.commutator_pi_pi_of_finite]
          congr 1
          funext i
          exact Group.IsPerfect.commutator_eq_top }
      let : Group.IsPerfect DR :=
        commutator_isPerfect_of_surjective_of_ker_le_center
          (prodRightPreimageProjection f')
          (prodRightPreimageProjection_surjective f' hf')
          (prodRightPreimageProjection_ker_le_center f' hker')
      let : Finite DR := inferInstance
      have hrRsurj : Function.Surjective rR :=
        prodRightPreimageDerivedProjection_surjective f' hf'
      have hrRker : rR.ker ≤ Subgroup.center DR := by
        intro x hx
        have hx' : (x : prodRightPreimage f') ∈
            (prodRightPreimageProjection f').ker := by
          have hx0 := hx
          rw [prodRightPreimageDerivedProjection_ker_eq_comap] at hx0
          exact hx0
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact Subgroup.mem_center_iff.mp
          (prodRightPreimageProjection_ker_le_center f' hker' hx') y
      have hrRp : IsPGroup p rR.ker := by
        rw [prodRightPreimageDerivedProjection_ker_eq_comap,
          prodRightPreimageProjection_ker_eq_comap]
        exact hkerp'.comap_subtype.comap_subtype
      have hright : rR.ker = ⊥ :=
        ih rR hrRsurj hrRker hrRp
      obtain ⟨s, _, hcomp⟩ :=
        exists_prod_section_isComplement'_of_component_derived_ker_eq_bot
          f' hf' hker' hleft hright
      have hker'bot : f'.ker = ⊥ :=
        central_subgroup_eq_bot_of_isPerfect_of_isComplement'
          f'.ker s.range hker' hcomp
      rw [← hker_eq]
      exact hker'bot

set_option backward.isDefEq.respectTransparency false in
/-- Any finite central extension of a finite alternating direct power splits
over a p-primary kernel when p does not divide the multiplier of one factor.
The section is obtained from the derived subgroup, whose induced covering has
trivial kernel by the preceding theorem. -/
public theorem exists_directPower_section_isComplement'_of_not_dvd_multiplier
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (q n : Nat)
    (f : H →* (Fin n → alternatingGroup (Fin (q + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker) :
    ∃ s : (Fin n → alternatingGroup (Fin (q + 5))) →* H,
      f.comp s = MonoidHom.id _ ∧ f.ker.IsComplement' s.range := by
  let A := alternatingGroup (Fin (q + 5))
  let D := commutator H
  let rD : D →* (Fin n → A) := f.comp D.subtype
  let : Group.IsPerfect A :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect (Fin n → A) := {
    commutator_eq_top := by
      change ⁅(⊤ : Subgroup (Fin n → A)), ⊤⁆ = ⊤
      rw [← Subgroup.pi_top (f := fun _ : Fin n => A) Set.univ]
      rw [Subgroup.commutator_pi_pi_of_finite]
      congr 1
      funext i
      exact Group.IsPerfect.commutator_eq_top }
  let : Group.IsPerfect D :=
    commutator_isPerfect_of_surjective_of_ker_le_center f hf hker
  let : Finite D := inferInstance
  have hrDsurj : Function.Surjective rD := by
    have hmap : D.map f = ⊤ := by
      dsimp [D]
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf]
      exact Group.IsPerfect.commutator_eq_top
    intro y
    have hy : y ∈ D.map f := by rw [hmap]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, hxy⟩
  have hrDker : rD.ker ≤ Subgroup.center D := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hker hx) y
  have hrDp : IsPGroup p rD.ker := by
    change IsPGroup p (f.ker.comap D.subtype)
    exact hkerp.comap_subtype
  have hrDbot : rD.ker = ⊥ :=
    directPowerCentralExtension_ker_eq_bot_of_not_dvd_multiplier
      q n rD hrDsurj hrDker hrDp hpM
  have hrDbij : Function.Bijective rD :=
    ⟨rD.ker_eq_bot_iff.mp hrDbot, hrDsurj⟩
  let e : D ≃* (Fin n → A) := MulEquiv.ofBijective rD hrDbij
  let s : (Fin n → A) →* H := D.subtype.comp e.symm.toMonoidHom
  have hsec : f.comp s = MonoidHom.id (Fin n → A) := by
    apply MonoidHom.ext
    intro x
    change rD (e.symm x) = x
    exact e.apply_symm_apply x
  have hdisj : Disjoint f.ker s.range := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    obtain ⟨y, rfl⟩ := hxR
    have hy : y = 1 := by
      have hxy : f (s y) = y := DFunLike.congr_fun hsec y
      have hfone : f (s y) = 1 := MonoidHom.mem_ker.mp hxK
      exact hxy.symm.trans hfone
    rw [hy]
    exact map_one s
  have hmul : (f.ker : Set H) * (s.range : Set H) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    let y := s (f x)
    let k := x * y⁻¹
    have hyf : f y = f x := by
      exact DFunLike.congr_fun hsec (f x)
    have hk : k ∈ f.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [k]
      rw [map_mul, map_inv, hyf]
      simp
    have hy : y ∈ s.range := ⟨f x, rfl⟩
    apply Set.mem_mul.mpr
    exact ⟨k, hk, y, hy, by simp [k]⟩
  exact ⟨s, hsec,
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul⟩

set_option backward.isDefEq.respectTransparency false in
/-- The one-factor specialization: a finite central extension of one
alternating group splits over a p-primary kernel when p does not divide its
multiplier. -/
public theorem exists_alternating_section_isComplement'_of_not_dvd_multiplier
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (q : Nat)
    (f : H →* alternatingGroup (Fin (q + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker) :
    ∃ s : alternatingGroup (Fin (q + 5)) →* H,
      f.comp s = MonoidHom.id _ ∧ f.ker.IsComplement' s.range := by
  let A := alternatingGroup (Fin (q + 5))
  let e : (Fin 1 → A) ≃* A := finOneArrowMulEquiv A
  let f' : H →* (Fin 1 → A) := e.symm.toMonoidHom.comp f
  have hf' : Function.Surjective f' := e.symm.surjective.comp hf
  have hker_eq : f'.ker = f.ker := by
    ext x
    change e.symm (f x) = 1 ↔ f x = 1
    constructor
    · intro hx
      apply e.symm.injective
      simpa using hx
    · intro hx
      simp [hx]
  have hker' : f'.ker ≤ Subgroup.center H := by
    rw [hker_eq]
    exact hker
  have hkerp' : IsPGroup p f'.ker := by
    rw [hker_eq]
    exact hkerp
  obtain ⟨s', hsec', hcomp'⟩ :=
    exists_directPower_section_isComplement'_of_not_dvd_multiplier
      q 1 f' hf' hker' hkerp' hpM
  let s : A →* H := s'.comp e.symm.toMonoidHom
  have hsec : f.comp s = MonoidHom.id A := by
    apply MonoidHom.ext
    intro a
    have h := DFunLike.congr_fun hsec' (e.symm a)
    change e.symm (f (s' (e.symm a))) = e.symm a at h
    exact e.symm.injective h
  have hrange : s.range = s'.range := by
    apply le_antisymm
    · rintro x ⟨a, rfl⟩
      exact ⟨e.symm a, rfl⟩
    · rintro x ⟨y, rfl⟩
      refine ⟨e y, ?_⟩
      change s' (e.symm (e y)) = s' y
      exact congrArg s' (e.symm_apply_apply y)
  rw [hker_eq, ← hrange] at hcomp'
  exact ⟨s, hsec, hcomp'⟩

end GLS3.Chapter5.SchurPresentation

/- Source: AlternatingPowerSemidirectExtension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Central extensions of alternating-power semidirect products

This module restricts a central extension of `N semidirectProduct A` to the
canonical base and top factors.  The preceding direct-power and one-factor
splitting theorems supply component sections; perfectness of the base then
forces their compatibility and produces a section of the whole semidirect
product.
-/


/-- Full preimage of the canonical normal factor in a semidirect product. -/
@[expose]
public def semidirectBasePreimage
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A) : Subgroup H :=
  (SemidirectProduct.rightHom : N ⋊[φ] A →* A).ker.comap f

/-- Projection from the base-factor preimage to the normal factor. -/
@[expose]
public def semidirectBasePreimageProjection
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A) :
    semidirectBasePreimage φ f →* N where
  toFun x := (f (x : H)).left
  map_one' := by simp
  map_mul' x y := by
    change (f ((x : H) * (y : H))).left =
      (f (x : H)).left * (f (y : H)).left
    rw [map_mul]
    have hx : (f (x : H)).right = 1 := MonoidHom.mem_ker.mp x.2
    simp [hx]

/-- The base-factor preimage projection is surjective. -/
public theorem semidirectBasePreimageProjection_surjective
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A)
    (hf : Function.Surjective f) :
    Function.Surjective (semidirectBasePreimageProjection φ f) := by
  intro n
  obtain ⟨x, hx⟩ := hf (SemidirectProduct.inl n)
  have hxE : x ∈ semidirectBasePreimage φ f := by
    change SemidirectProduct.rightHom (f x) = 1
    rw [hx]
    simp
  refine ⟨⟨x, hxE⟩, ?_⟩
  change (f x).left = n
  exact congrArg SemidirectProduct.left hx

/-- The base-factor kernel is the restriction of the global kernel. -/
public theorem semidirectBasePreimageProjection_ker_eq_comap
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A) :
    (semidirectBasePreimageProjection φ f).ker =
      f.ker.comap (semidirectBasePreimage φ f).subtype := by
  ext x
  constructor
  · intro hx
    change f (x : H) = 1
    apply SemidirectProduct.ext
    · change (f (x : H)).left = 1
      exact MonoidHom.mem_ker.mp hx
    · exact MonoidHom.mem_ker.mp x.2
  · intro hx
    rw [MonoidHom.mem_ker]
    change (f (x : H)).left = 1
    exact congrArg SemidirectProduct.left (MonoidHom.mem_ker.mp hx)

/-- A central global kernel induces a central base-factor kernel. -/
public theorem semidirectBasePreimageProjection_ker_le_center
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A)
    (hker : f.ker ≤ Subgroup.center H) :
    (semidirectBasePreimageProjection φ f).ker ≤
      Subgroup.center (semidirectBasePreimage φ f) := by
  rw [semidirectBasePreimageProjection_ker_eq_comap]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hx) y

/-- Full preimage of the canonical top factor in a semidirect product. -/
@[expose]
public def semidirectTopPreimage
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A) : Subgroup H :=
  SemidirectProduct.inr.range.comap f

/-- Projection from the top-factor preimage to the acting factor. -/
@[expose]
public def semidirectTopPreimageProjection
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A) :
    semidirectTopPreimage φ f →* A :=
  SemidirectProduct.rightHom.comp
    (f.comp (semidirectTopPreimage φ f).subtype)

/-- The top-factor preimage projection is surjective. -/
public theorem semidirectTopPreimageProjection_surjective
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A)
    (hf : Function.Surjective f) :
    Function.Surjective (semidirectTopPreimageProjection φ f) := by
  intro a
  obtain ⟨x, hx⟩ := hf (SemidirectProduct.inr a)
  have hxE : x ∈ semidirectTopPreimage φ f := by
    change f x ∈ SemidirectProduct.inr.range
    exact ⟨a, hx.symm⟩
  exact ⟨⟨x, hxE⟩, congrArg SemidirectProduct.right hx⟩

/-- The top-factor kernel is the restriction of the global kernel. -/
public theorem semidirectTopPreimageProjection_ker_eq_comap
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A) :
    (semidirectTopPreimageProjection φ f).ker =
      f.ker.comap (semidirectTopPreimage φ f).subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := x.2
    change f (x : H) = 1
    have hright : (f (x : H)).right = 1 := MonoidHom.mem_ker.mp hx
    have ha1 : a = 1 := by
      exact (congrArg SemidirectProduct.right ha).trans hright
    rw [← ha, ha1]
    rfl
  · intro hx
    rw [MonoidHom.mem_ker]
    change (f (x : H)).right = 1
    exact congrArg SemidirectProduct.right (MonoidHom.mem_ker.mp hx)

/-- A central global kernel induces a central top-factor kernel. -/
public theorem semidirectTopPreimageProjection_ker_le_center
    {H : Type __ch5_SemidirectExtension_u} {N : Type __ch5_SemidirectExtension_v} {A : Type __ch5_SemidirectExtension_w}
    [Group H] [Group N] [Group A]
    (φ : A →* MulAut N) (f : H →* N ⋊[φ] A)
    (hker : f.ker ≤ Subgroup.center H) :
    (semidirectTopPreimageProjection φ f).ker ≤
      Subgroup.center (semidirectTopPreimage φ f) := by
  rw [semidirectTopPreimageProjection_ker_eq_comap]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hx) y

set_option backward.isDefEq.respectTransparency false in
/-- A central extension of an alternating direct power by an alternating top
factor splits whenever the p-primary global kernel has no contribution from
either the base-factor multiplier or the top-factor multiplier. -/
public theorem
    exists_alternatingPowerSemidirect_section_isComplement'_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (qBase qTop n : Nat)
    (φ : alternatingGroup (Fin (qTop + 5)) →*
      MulAut (Fin n → alternatingGroup (Fin (qBase + 5))))
    (f : H →* (Fin n → alternatingGroup (Fin (qBase + 5))) ⋊[φ]
      alternatingGroup (Fin (qTop + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpBase : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qBase).toMonoidHom.ker)
    (hpTop : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qTop).toMonoidHom.ker) :
    ∃ s, f.comp s = MonoidHom.id _ ∧ f.ker.IsComplement' s.range := by
  let N := Fin n → alternatingGroup (Fin (qBase + 5))
  let A := alternatingGroup (Fin (qTop + 5))
  let EB := semidirectBasePreimage φ f
  let rB := semidirectBasePreimageProjection φ f
  have hrBsurj : Function.Surjective rB :=
    semidirectBasePreimageProjection_surjective φ f hf
  have hrBker : rB.ker ≤ Subgroup.center EB :=
    semidirectBasePreimageProjection_ker_le_center φ f hker
  have hrBp : IsPGroup p rB.ker := by
    rw [semidirectBasePreimageProjection_ker_eq_comap]
    exact hkerp.comap_subtype
  obtain ⟨tB, htB, _⟩ :=
    exists_directPower_section_isComplement'_of_not_dvd_multiplier
      qBase n rB hrBsurj hrBker hrBp hpBase
  let sN : N →* H := EB.subtype.comp tB
  have hsN : f.comp sN = SemidirectProduct.inl := by
    apply MonoidHom.ext
    intro x
    apply SemidirectProduct.ext
    · have hx := DFunLike.congr_fun htB x
      change rB (tB x) = x at hx
      exact hx
    · exact MonoidHom.mem_ker.mp (tB x).2
  let ET := semidirectTopPreimage φ f
  let rA := semidirectTopPreimageProjection φ f
  have hrAsurj : Function.Surjective rA :=
    semidirectTopPreimageProjection_surjective φ f hf
  have hrAker : rA.ker ≤ Subgroup.center ET :=
    semidirectTopPreimageProjection_ker_le_center φ f hker
  have hrAp : IsPGroup p rA.ker := by
    rw [semidirectTopPreimageProjection_ker_eq_comap]
    exact hkerp.comap_subtype
  obtain ⟨tA, htA, _⟩ :=
    exists_alternating_section_isComplement'_of_not_dvd_multiplier
      qTop rA hrAsurj hrAker hrAp hpTop
  let sA : A →* H := ET.subtype.comp tA
  have hsA : f.comp sA = SemidirectProduct.inr := by
    apply MonoidHom.ext
    intro a
    change f ((ET.subtype) (tA a)) = SemidirectProduct.inr a
    obtain ⟨b, hb⟩ := (tA a).2
    have hright := DFunLike.congr_fun htA a
    change (f ((ET.subtype) (tA a))).right = a at hright
    apply SemidirectProduct.ext
    · exact (congrArg SemidirectProduct.left hb).symm
    · exact hright
  let : Group.IsPerfect (alternatingGroup (Fin (qBase + 5))) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect N := {
    commutator_eq_top := by
      change ⁅(⊤ : Subgroup N), ⊤⁆ = ⊤
      rw [← Subgroup.pi_top
        (f := fun _ : Fin n => alternatingGroup (Fin (qBase + 5))) Set.univ]
      rw [Subgroup.commutator_pi_pi_of_finite]
      congr 1
      funext i
      exact Group.IsPerfect.commutator_eq_top }
  exact exists_semidirectProduct_section_isComplement'_of_component_sections
    φ f hker sN sA hsN hsA

end GLS3.Chapter5.SchurPresentation
/- END Theory.SemidirectExtension -/

/- BEGIN Theory.Reduction -/
noncomputable section

/- Source: OddPBlockContainment.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Odd-primary containment in alternating block subgroups

An odd-primary permutation group preserving two blocks acts by even
permutations on each block: either component sign would otherwise give a
nontrivial quotient of order two.  This upgrades containment in the full
symmetric block subgroup to containment in `A_a × A_b` and connects the
permutation-theoretic block condition to the central-extension splitting
contradiction.
-/

private theorem __ch5_Reduction_map_eq_one_of_isPGroup_to_unitsInt
    {P : Type*} [Group P] {p : Nat} [Fact p.Prime]
    (hP : IsPGroup p P) (hp2 : p ≠ 2)
    (χ : P →* ℤˣ) (x : P) : χ x = 1 := by
  have hRp : IsPGroup p χ.range :=
    hP.of_surjective χ.rangeRestrict χ.rangeRestrict_surjective
  have hRdvd : Nat.card χ.range ∣ 2 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_units_int] using
      Subgroup.card_subgroup_dvd_card χ.range
  have hRcard : Nat.card χ.range = 1 := by
    rcases hRp.card_eq_or_dvd with h1 | hp
    · exact h1
    · have hp2dvd : p ∣ 2 := hp.trans hRdvd
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hp2dvd
      have hpge : 2 ≤ p := (Fact.out : p.Prime).two_le
      exact False.elim (hp2 (Nat.le_antisymm hple hpge))
  have hRbot : χ.range = ⊥ := Subgroup.card_eq_one.mp hRcard
  have hx : χ x ∈ χ.range := ⟨x, rfl⟩
  rw [hRbot] at hx
  exact Subgroup.mem_bot.mp hx

set_option backward.isDefEq.respectTransparency false in
/-- An odd-primary subgroup of the full symmetric block subgroup is already
contained in the alternating block subgroup. -/
public theorem range_le_alternatingProdBlockHom_range_of_isPGroup_of_permBlock
    {P : Type*} [Group P] {p : Nat} [Fact p.Prime]
    (hP : IsPGroup p P) (hp2 : p ≠ 2)
    (a b : Nat)
    (g : P →* alternatingGroup (Fin (a + b)))
    (hblock : ∀ x : P, ((g x : alternatingGroup (Fin (a + b))) :
      Equiv.Perm (Fin (a + b))) ∈ (permProdBlockHom a b).range) :
    g.range ≤ (alternatingProdBlockHom a b).range := by
  let i := permProdBlockHom a b
  let e := MonoidHom.ofInjective (permProdBlockHom_injective a b)
  let gPerm : P →* Equiv.Perm (Fin (a + b)) :=
    (alternatingGroup (Fin (a + b))).subtype.comp g
  let gBlock : P →* i.range :=
    gPerm.codRestrict i.range hblock
  let c : P →* Equiv.Perm (Fin a) × Equiv.Perm (Fin b) :=
    e.symm.toMonoidHom.comp gBlock
  let χA : P →* ℤˣ :=
    Equiv.Perm.sign.comp ((MonoidHom.fst _ _).comp c)
  let χB : P →* ℤˣ :=
    Equiv.Perm.sign.comp ((MonoidHom.snd _ _).comp c)
  have hχA (x : P) : Equiv.Perm.sign (c x).1 = 1 :=
    __ch5_Reduction_map_eq_one_of_isPGroup_to_unitsInt hP hp2 χA x
  have hχB (x : P) : Equiv.Perm.sign (c x).2 = 1 :=
    __ch5_Reduction_map_eq_one_of_isPGroup_to_unitsInt hP hp2 χB x
  rintro z ⟨x, rfl⟩
  let xA : alternatingGroup (Fin a) :=
    ⟨(c x).1, Equiv.Perm.mem_alternatingGroup.mpr (hχA x)⟩
  let xB : alternatingGroup (Fin b) :=
    ⟨(c x).2, Equiv.Perm.mem_alternatingGroup.mpr (hχB x)⟩
  refine ⟨(xA, xB), ?_⟩
  apply Subtype.ext
  rw [coe_alternatingProdBlockHom_apply]
  have hc := congrArg Subtype.val (e.apply_symm_apply (gBlock x))
  rw [MonoidHom.ofInjective_apply] at hc
  have hgb : ((gBlock x : i.range) : Equiv.Perm (Fin (a + b))) =
      (g x : Equiv.Perm (Fin (a + b))) := rfl
  change i (c x) = (g x : Equiv.Perm (Fin (a + b)))
  exact hc.trans hgb

/-- An odd Sylow subgroup whose image preserves the two standard blocks lies
in the full preimage of the alternating block subgroup. -/
public theorem sylow_le_alternatingBlockPreimage_of_permBlock
    {H : Type*} [Group H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (a b : Nat)
    (f : H →* alternatingGroup (Fin (a + b)))
    (P : Sylow p H)
    (hblock : ∀ x : P,
      ((f (x : H) : alternatingGroup (Fin (a + b))) :
        Equiv.Perm (Fin (a + b))) ∈ (permProdBlockHom a b).range) :
    (P : Subgroup H) ≤ alternatingBlockPreimage a b f := by
  let g : P →* alternatingGroup (Fin (a + b)) :=
    f.comp (P : Subgroup H).subtype
  have hg : g.range ≤ (alternatingProdBlockHom a b).range :=
    range_le_alternatingProdBlockHom_range_of_isPGroup_of_permBlock
      P.isPGroup' hp2 a b g hblock
  intro x hx
  let xp : P := ⟨x, hx⟩
  exact hg ⟨xp, rfl⟩

/-- If both smaller alternating multipliers have no `p`-part, a nontrivial
odd-primary central kernel prevents a Sylow image from preserving the two
standard blocks. -/
public theorem not_sylow_image_le_permBlock_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker)
    (P : Sylow p H) :
    ¬ ∀ x : P,
      ((f (x : H) : alternatingGroup
          (Fin ((qA + 5) + (qB + 5)))) :
        Equiv.Perm (Fin ((qA + 5) + (qB + 5)))) ∈
          (permProdBlockHom (qA + 5) (qB + 5)).range := by
  intro hblock
  exact not_sylow_le_alternatingBlockPreimage_of_not_dvd_multipliers
    qA qB f hf hker hkerp hpker hpMA hpMB P
    (sylow_le_alternatingBlockPreimage_of_permBlock
      hp2 (qA + 5) (qB + 5) f P hblock)

end GLS3.Chapter5.SchurPresentation

/- Source: StandardBlockReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Standard two-block preservation

Preserving the first `a` points of `Fin (a+b)` is equivalent to lying in the
standard symmetric block subgroup.  Combined with the odd-primary containment
and central-extension splitting results, this excludes such a Sylow image when
both smaller alternating multipliers have no `p`-part.
-/

/-- The first `a` points in the standard decomposition `Fin (a+b)`. -/
@[expose]
public def finFirstBlock (a b : Nat) : Set (Fin (a + b)) :=
  Set.range (Fin.castAdd b)

/-- A permutation preserving the first standard block lies in `S_a × S_b`. -/
public theorem perm_mem_permProdBlockHom_range_of_mapsTo_finFirstBlock
    (a b : Nat) (σ : Equiv.Perm (Fin (a + b)))
    (hσ : Set.MapsTo σ (finFirstBlock a b) (finFirstBlock a b)) :
    σ ∈ (permProdBlockHom a b).range := by
  let τ : Equiv.Perm (Fin a ⊕ Fin b) :=
    finSumFinEquiv.symm.permCongr σ
  have hτ : Set.MapsTo τ (Set.range Sum.inl) (Set.range Sum.inl) := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hσ ⟨i, rfl⟩
    refine ⟨j, ?_⟩
    simpa [τ] using congrArg finSumFinEquiv.symm hj
  obtain ⟨x, hx⟩ :=
    Equiv.Perm.mem_sumCongrHom_range_of_perm_mapsTo_inl hτ
  change Equiv.Perm.sumCongr x.1 x.2 = τ at hx
  refine ⟨x, ?_⟩
  rw [permProdBlockHom_apply]
  rw [hx]
  ext i
  simp [τ, Equiv.permCongr_apply]

/-- Under the two smaller multiplier hypotheses, a Sylow image cannot preserve
the first standard block. -/
public theorem not_sylow_image_mapsTo_finFirstBlock_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker)
    (P : Sylow p H) :
    ¬ ∀ x : P, Set.MapsTo
      (f (x : H) : Fin ((qA + 5) + (qB + 5)) →
        Fin ((qA + 5) + (qB + 5)))
      (finFirstBlock (qA + 5) (qB + 5))
      (finFirstBlock (qA + 5) (qB + 5)) := by
  intro hmaps
  apply not_sylow_image_le_permBlock_of_not_dvd_multipliers
    hp2 qA qB f hf hker hkerp hpker hpMA hpMB P
  intro x
  exact perm_mem_permProdBlockHom_range_of_mapsTo_finFirstBlock
    (qA + 5) (qB + 5) _ (hmaps x)

end GLS3.Chapter5.SchurPresentation

/- Source: RelabeledBlockReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Relabeled two-block preservation

Conjugating by an equivalence of the point set transports any block of the
right size to the standard first block without changing the central extension
kernel.  Thus the standard block exclusion applies to arbitrary relabeled
two-block decompositions.
-/

/-- The image of the standard first block under a relabeling equivalence. -/
@[expose]
public def equivImageFirstBlock (a b : Nat) (e : Fin (a + b) ≃ Fin (a + b)) :
    Set (Fin (a + b)) :=
  e '' finFirstBlock a b

/-- Under the two smaller multiplier hypotheses, a Sylow image cannot preserve
any relabeling of the standard first block. -/
public theorem not_sylow_image_mapsTo_equivImageFirstBlock_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker)
    (P : Sylow p H)
    (e : Fin ((qA + 5) + (qB + 5)) ≃
      Fin ((qA + 5) + (qB + 5))) :
    ¬ ∀ x : P, Set.MapsTo
      (f (x : H) : Fin ((qA + 5) + (qB + 5)) →
        Fin ((qA + 5) + (qB + 5)))
      (equivImageFirstBlock (qA + 5) (qB + 5) e)
      (equivImageFirstBlock (qA + 5) (qB + 5) e) := by
  intro hmaps
  let eA := e.symm.altCongrHom
  let f' : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))) :=
    eA.toMonoidHom.comp f
  have hf'ker : f'.ker = f.ker :=
    MonoidHom.ker_comp_of_injective f eA.toMonoidHom eA.injective
  have hf'surj : Function.Surjective f' := eA.surjective.comp hf
  have hf'center : f'.ker ≤ Subgroup.center H := by
    rw [hf'ker]
    exact hker
  have hf'p : IsPGroup p f'.ker := by
    rw [hf'ker]
    exact hkerp
  have hpker' : p ∣ Nat.card f'.ker := by
    rw [hf'ker]
    exact hpker
  apply not_sylow_image_mapsTo_finFirstBlock_of_not_dvd_multipliers
    hp2 qA qB f' hf'surj hf'center hf'p hpker' hpMA hpMB P
  intro x y hy
  have hey : e y ∈ equivImageFirstBlock (qA + 5) (qB + 5) e :=
    ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzEq⟩ := hmaps x hey
  change e.symm ((f (x : H) : Equiv.Perm _) (e y)) ∈
    finFirstBlock (qA + 5) (qB + 5)
  rw [← hzEq, e.symm_apply_apply]
  exact hz

end GLS3.Chapter5.SchurPresentation

/- Source: InvariantSubsetReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Invariant-subset block reduction

An invariant subset and its complement, together with their cardinalities,
canonically determine a relabeling of the standard two-block decomposition.
This removes all coordinate choices from the block-exclusion endpoint.
-/

/-- A relabeling carrying the standard first block onto `S`. -/
public noncomputable def relabelingEquivOfSubset
    (a b : Nat) (S : Set (Fin (a + b)))
    (hS : Nat.card S = a) (hSc : Nat.card (Sᶜ : Set (Fin (a + b))) = b) :
    Fin (a + b) ≃ Fin (a + b) := by
  classical
  let eS : Fin a ≃ S :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hS)).symm
  let eSc : Fin b ≃ (Sᶜ : Set (Fin (a + b))) :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hSc)).symm
  exact finSumFinEquiv.symm.trans
    ((eS.sumCongr eSc).trans (Equiv.Set.sumCompl S))

/-- The relabeling constructed from `S` sends the standard first block to `S`. -/
public theorem equivImageFirstBlock_relabelingEquivOfSubset
    (a b : Nat) (S : Set (Fin (a + b)))
    (hS : Nat.card S = a) (hSc : Nat.card (Sᶜ : Set (Fin (a + b))) = b) :
    equivImageFirstBlock a b (relabelingEquivOfSubset a b S hS hSc) = S := by
  classical
  let eS : Fin a ≃ S :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hS)).symm
  let eSc : Fin b ≃ (Sᶜ : Set (Fin (a + b))) :=
    (Fintype.equivFinOfCardEq (by
      simpa [Nat.card_eq_fintype_card] using hSc)).symm
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    simp [relabelingEquivOfSubset]
  · intro hx
    obtain ⟨i, hi⟩ := eS.surjective ⟨x, hx⟩
    refine ⟨Fin.castAdd b i, ⟨i, rfl⟩, ?_⟩
    simpa [relabelingEquivOfSubset, eS, eSc] using congrArg Subtype.val hi

/-- Under the two smaller multiplier hypotheses, a Sylow image cannot preserve
an arbitrary subset whose two block sizes are the prescribed values. -/
public theorem not_sylow_image_mapsTo_subset_of_cards_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (qA qB : Nat)
    (f : H →* alternatingGroup (Fin ((qA + 5) + (qB + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker)
    (P : Sylow p H)
    (S : Set (Fin ((qA + 5) + (qB + 5))))
    (hS : Nat.card S = qA + 5)
    (hSc : Nat.card (Sᶜ : Set (Fin ((qA + 5) + (qB + 5)))) = qB + 5) :
    ¬ ∀ x : P, Set.MapsTo
      (f (x : H) : Fin ((qA + 5) + (qB + 5)) →
        Fin ((qA + 5) + (qB + 5))) S S := by
  intro hmaps
  let e := relabelingEquivOfSubset (qA + 5) (qB + 5) S hS hSc
  apply not_sylow_image_mapsTo_equivImageFirstBlock_of_not_dvd_multipliers
    hp2 qA qB f hf hker hkerp hpker hpMA hpMB P e
  intro x
  rw [equivImageFirstBlock_relabelingEquivOfSubset]
  exact hmaps x

/-- Version with independent block-size variables identified with the two
canonical alternating degrees. -/
public theorem not_sylow_image_mapsTo_subset_of_card_eq_add_five
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (a b qA qB : Nat) (ha : a = qA + 5) (hb : b = qB + 5)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qA).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qB).toMonoidHom.ker)
    (P : Sylow p H)
    (S : Set (Fin (a + b)))
    (hS : Nat.card S = a)
    (hSc : Nat.card (Sᶜ : Set (Fin (a + b))) = b) :
    ¬ ∀ x : P, Set.MapsTo
      (f (x : H) : Fin (a + b) → Fin (a + b)) S S := by
  subst a
  subst b
  exact not_sylow_image_mapsTo_subset_of_cards_of_not_dvd_multipliers
    hp2 qA qB f hf hker hkerp hpker hpMA hpMB P S hS hSc

/-- Block-size form used by orbit reductions: if both an invariant subset and
its complement have at least five points, their smaller multiplier indices
are obtained by subtracting five. -/
public theorem not_sylow_image_mapsTo_subset_of_five_le_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (a b : Nat) (ha5 : 5 ≤ a) (hb5 : 5 ≤ b)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering (a - 5)).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering (b - 5)).toMonoidHom.ker)
    (P : Sylow p H)
    (S : Set (Fin (a + b)))
    (hS : Nat.card S = a)
    (hSc : Nat.card (Sᶜ : Set (Fin (a + b))) = b) :
    ¬ ∀ x : P, Set.MapsTo
      (f (x : H) : Fin (a + b) → Fin (a + b)) S S := by
  exact not_sylow_image_mapsTo_subset_of_card_eq_add_five
    hp2 a b (a - 5) (b - 5)
    (Nat.sub_add_cancel ha5).symm (Nat.sub_add_cancel hb5).symm
    f hf hker hkerp hpker hpMA hpMB P S hS hSc

/-- The preceding block-size theorem with an independently named total degree. -/
public theorem
    not_sylow_image_mapsTo_subset_of_total_eq_of_five_le_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (m a b : Nat) (hm : m = a + b) (ha5 : 5 ≤ a) (hb5 : 5 ≤ b)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering (a - 5)).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering (b - 5)).toMonoidHom.ker)
    (P : Sylow p H)
    (S : Set (Fin m))
    (hS : Nat.card S = a)
    (hSc : Nat.card (Sᶜ : Set (Fin m)) = b) :
    ¬ ∀ x : P, Set.MapsTo (f (x : H) : Fin m → Fin m) S S := by
  subst m
  exact not_sylow_image_mapsTo_subset_of_five_le_of_not_dvd_multipliers
    hp2 a b ha5 hb5 f hf hker hkerp hpker hpMA hpMB P S hS hSc

end GLS3.Chapter5.SchurPresentation

/- Source: OrbitBlockReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! ## Orbit reduction for odd-primary Sylow images

For `p ≥ 5`, a nontrivial proper orbit of a Sylow image and its complement
both have size divisible by `p`, hence at least five.  The invariant-subset
block reduction then contradicts the inductive absence of `p` in smaller
alternating multipliers.  Thus a minimal-counterexample Sylow image is
transitive and the degree is a power of `p`.
-/

/-- A prescribed Sylow-image orbit split with both parts at least five is
incompatible with the two smaller multiplier hypotheses. -/
public theorem false_of_sylow_image_orbit_card_split_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2)
    (a b : Nat) (ha5 : 5 ≤ a) (hb5 : 5 ≤ b)
    (f : H →* alternatingGroup (Fin (a + b)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpMA : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering (a - 5)).toMonoidHom.ker)
    (hpMB : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering (b - 5)).toMonoidHom.ker)
    (P : Sylow p H) (y : Fin (a + b))
    (hS : Nat.card (MulAction.orbit (P.mapSurjective hf) y) = a)
    (hSc : Nat.card
      ((MulAction.orbit (P.mapSurjective hf) y)ᶜ : Set (Fin (a + b))) = b) :
    False := by
  let Q : Sylow p (alternatingGroup (Fin (a + b))) := P.mapSurjective hf
  let S : Set (Fin (a + b)) := MulAction.orbit Q y
  apply not_sylow_image_mapsTo_subset_of_five_le_of_not_dvd_multipliers
    hp2 a b ha5 hb5 f hf hker hkerp hpker hpMA hpMB P S hS hSc
  intro x
  let q : Q := ⟨f (x : H), ⟨x, x.2, rfl⟩⟩
  exact MulAction.mapsTo_smul_orbit q y

/-- A moved proper orbit contradicts the inductive absence of `p` in all
smaller alternating multipliers. -/
public theorem false_of_proper_moved_sylow_image_orbit_of_not_dvd_multipliers
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (m : Nat) (hpdeg : p ∣ m)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (P : Sylow p H) (y : Fin m)
    (hmove : ∃ q : P.mapSurjective hf, q • y ≠ y)
    (hproper : MulAction.orbit (P.mapSurjective hf) y ≠ Set.univ)
    (hsmall : ∀ d : Nat, 5 ≤ d → d < m →
      ¬ p ∣ Nat.card
        (alternatingFreeCentralCovering (d - 5)).toMonoidHom.ker) :
    False := by
  let Q : Sylow p (alternatingGroup (Fin m)) := P.mapSurjective hf
  let S : Set (Fin m) := MulAction.orbit Q y
  let a := Nat.card S
  let b := Nat.card (Sᶜ : Set (Fin m))
  let : Fintype (MulAction.orbit Q y) := Fintype.ofFinite _
  have hsum : m = a + b := by
    have h := Set.ncard_add_ncard_compl S
    simpa [a, b, Nat.card_fin, add_comm] using h.symm
  obtain ⟨q, hqy⟩ := hmove
  have hyNotFixed : y ∉ MulAction.fixedPoints Q (Fin m) := by
    intro hy
    exact hqy (MulAction.mem_fixedPoints.mp hy q)
  have ha1 : a ≠ 1 := by
    intro ha
    apply hyNotFixed
    rw [MulAction.mem_fixedPoints_iff_card_orbit_eq_one]
    simpa [a, S, Nat.card_eq_fintype_card] using ha
  obtain ⟨r, hr⟩ := Q.isPGroup'.card_orbit y
  have hr0 : r ≠ 0 := by
    intro hrzero
    subst r
    apply ha1
    change Nat.card (MulAction.orbit Q y) = 1
    simpa only [pow_zero] using hr
  have hpa : p ∣ a := by
    rw [show a = Nat.card (MulAction.orbit Q y) by rfl, hr]
    exact dvd_pow_self p hr0
  have haPos : 0 < a := by
    exact (show S.Nonempty from ⟨y, MulAction.mem_orbit_self y⟩).ncard_pos
  have ha5 : 5 ≤ a := hp5.trans (Nat.le_of_dvd haPos hpa)
  have hpab : p ∣ a + b := by
    rw [← hsum]
    exact hpdeg
  have hpb : p ∣ b := (Nat.dvd_add_iff_right hpa).mpr hpab
  have hScNonempty : (Sᶜ : Set (Fin m)).Nonempty := by
    apply Set.ssubset_univ_iff_nonempty_compl.mp
    exact Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, hproper⟩
  have hbPos : 0 < b := by
    exact hScNonempty.ncard_pos
  have hb5 : 5 ≤ b := hp5.trans (Nat.le_of_dvd hbPos hpb)
  have haLt : a < m := by omega
  have hbLt : b < m := by omega
  have hpMS := hsmall a ha5 haLt
  have hpMSc := hsmall b hb5 hbLt
  apply not_sylow_image_mapsTo_subset_of_total_eq_of_five_le_of_not_dvd_multipliers
    hp2 m a b hsum ha5 hb5 f hf hker hkerp hpker hpMS hpMSc P S rfl rfl
  intro x
  let qx : Q := ⟨f (x : H), ⟨x, x.2, rfl⟩⟩
  exact MulAction.mapsTo_smul_orbit qx y

/-- The nontransitive branch of the odd-prime minimal-counterexample argument
is impossible. -/
public theorem false_of_not_pretransitive_sylow_image_of_inductive_not_dvd
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (m : Nat) (hpdeg : p ∣ m)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (P : Sylow p H)
    (hnotTrans : ¬ MulAction.IsPretransitive
      (P.mapSurjective hf) (Fin m))
    (hsmall : ∀ d : Nat, 5 ≤ d → d < m →
      ¬ p ∣ Nat.card
        (alternatingFreeCentralCovering (d - 5)).toMonoidHom.ker) :
    False := by
  let Q : Sylow p (alternatingGroup (Fin m)) := P.mapSurjective hf
  have hpBase : p ∣ Nat.card (alternatingGroup (Fin m)) :=
    prime_dvd_card_of_dvd_card_ker f hf hker hpker
  have hQne : (Q : Subgroup (alternatingGroup (Fin m))) ≠ ⊥ :=
    Q.ne_bot_of_dvd_card hpBase
  obtain ⟨q, hqQ, hq1⟩ : ∃ q : alternatingGroup (Fin m),
      q ∈ (Q : Subgroup (alternatingGroup (Fin m))) ∧ q ≠ 1 := by
    by_contra h
    push Not at h
    apply hQne
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    exact h q hq
  let qQ : Q := ⟨q, hqQ⟩
  obtain ⟨y, hqy⟩ : ∃ y : Fin m, qQ • y ≠ y := by
    by_contra h
    push Not at h
    apply hq1
    apply Subtype.ext
    ext y
    have hy := h y
    change (q : Equiv.Perm (Fin m)) y = y at hy
    exact congrArg Fin.val hy
  have hproper : MulAction.orbit Q y ≠ Set.univ := by
    intro htop
    exact hnotTrans
      ((MulAction.isPretransitive_iff_orbit_eq_univ y).mpr htop)
  exact false_of_proper_moved_sylow_image_orbit_of_not_dvd_multipliers
    hp2 hp5 m hpdeg f hf hker hkerp hpker P y ⟨qQ, hqy⟩ hproper hsmall

/-- In the odd-prime minimal-counterexample range `p ≥ 5`, the Sylow image
must be transitive: every nontransitive orbit gives a forbidden two-block
splitting. -/
public theorem isPretransitive_sylow_image_of_inductive_not_dvd
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (m : Nat) (hpdeg : p ∣ m)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (P : Sylow p H)
    (hsmall : ∀ d : Nat, 5 ≤ d → d < m →
      ¬ p ∣ Nat.card
        (alternatingFreeCentralCovering (d - 5)).toMonoidHom.ker) :
    MulAction.IsPretransitive (P.mapSurjective hf) (Fin m) := by
  by_contra hnot
  exact false_of_not_pretransitive_sylow_image_of_inductive_not_dvd
    hp2 hp5 m hpdeg f hf hker hkerp hpker P hnot hsmall

/-- Consequently, the permutation degree is a power of `p`. -/
public theorem exists_degree_eq_prime_pow_of_inductive_not_dvd
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime] (hp2 : p ≠ 2) (hp5 : 5 ≤ p)
    (m : Nat) (hm0 : 0 < m) (hpdeg : p ∣ m)
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (P : Sylow p H)
    (hsmall : ∀ d : Nat, 5 ≤ d → d < m →
      ¬ p ∣ Nat.card
        (alternatingFreeCentralCovering (d - 5)).toMonoidHom.ker) :
    ∃ r : Nat, m = p ^ r := by
  let Q : Sylow p (alternatingGroup (Fin m)) := P.mapSurjective hf
  let : MulAction.IsPretransitive Q (Fin m) :=
    isPretransitive_sylow_image_of_inductive_not_dvd
      hp2 hp5 m hpdeg f hf hker hkerp hpker P hsmall
  let y : Fin m := ⟨0, hm0⟩
  obtain ⟨r, hr⟩ := Q.isPGroup'.card_orbit y
  refine ⟨r, ?_⟩
  have hcard : Nat.card (MulAction.orbit Q y) = m := by
    rw [MulAction.orbit_eq_univ]
    simp
  exact hcard.symm.trans hr

end GLS3.Chapter5.SchurPresentation

/- Source: PointStabilizerReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

open RootAm

/-! ## A1 33.20: the point-stabilizer reduction

If a Sylow `p`-subgroup of a central extension has image acting on a number
of points not divisible by `p`, its image fixes a point.  After conjugating
that point to the final coordinate, the Sylow subgroup lies over the standard
root `A_{m-1}`.  The inductive root splitting and A1 33.11 then force a
nontrivial central `p`-kernel to vanish.
-/

/-- The standard root on the first `n+4` points is exactly the stabilizer of
the final point in `A_{n+5}`. -/
public theorem rootAm_pred_eq_stabilizer_last (n : Nat) (hn : 1 ≤ n) :
    rootAm n (n + 4) (by omega) =
      MulAction.stabilizer (alternatingGroup (Fin (n + 5))) (Fin.last (n + 4)) := by
  let R := rootAm n (n + 4) (by omega)
  let S := MulAction.stabilizer
    (alternatingGroup (Fin (n + 5))) (Fin.last (n + 4))
  have hle : R ≤ S := by
    rintro σ ⟨τ, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change tailPermHom n (n + 4) (by omega) τ.1 (Fin.last (n + 4)) =
      Fin.last (n + 4)
    unfold tailPermHom
    rw [Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_notMem]
    rintro ⟨i, hi⟩
    have hi' := congrArg Fin.val hi
    simp [tailEmbedding] at hi'
    omega
  have hR2 : 2 * Nat.card R = (n + 4).factorial := by
    let e := centralRootAmEquiv n (n + 4) (by omega)
    rw [← Nat.card_congr e.toEquiv]
    have h := two_mul_nat_card_alternatingGroup
      (α := Fin (((n + 4) - 5) + 5))
    rw [Nat.card_perm] at h
    have hdim : n - 1 + 5 = n + 4 := by omega
    simpa [Nat.card_fin, hdim] using h
  let : MulAction.IsPretransitive
      (alternatingGroup (Fin (n + 5))) (Fin (n + 5)) :=
    alternatingGroup.isPretransitive_of_three_le_card _ (by simp)
  have hSindex : S.index = n + 5 := by
    simpa [S] using
      (MulAction.index_stabilizer_of_transitive
        (alternatingGroup (Fin (n + 5))) (Fin.last (n + 4)))
  have hSmul : (n + 5) * Nat.card S =
      Nat.card (alternatingGroup (Fin (n + 5))) := by
    calc
      (n + 5) * Nat.card S = S.index * Nat.card S := by rw [hSindex]
      _ = Nat.card (alternatingGroup (Fin (n + 5))) := S.index_mul_card
  have hA2 : 2 * Nat.card (alternatingGroup (Fin (n + 5))) =
      (n + 5).factorial := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin (n + 5))
    rw [Nat.card_perm] at h
    simpa [Nat.card_fin] using h
  have hAeq : Nat.card (alternatingGroup (Fin (n + 5))) =
      (n + 5) * Nat.card R := by
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
    calc
      2 * Nat.card (alternatingGroup (Fin (n + 5))) = (n + 5).factorial := hA2
      _ = (n + 5) * (n + 4).factorial := by
        rw [show n + 5 = (n + 4) + 1 by omega, Nat.factorial_succ]
      _ = (n + 5) * (2 * Nat.card R) := by rw [hR2]
      _ = 2 * ((n + 5) * Nat.card R) := by ac_rfl
  have hcard : Nat.card S = Nat.card R := by
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < n + 5)
      (hSmul.trans hAeq)
  exact Subgroup.eq_of_le_of_card_ge hle hcard.le

/-- If `p` does not divide the degree, a conjugate Sylow `p`-subgroup lies
in the full preimage of the standard point stabilizer `A_{n+4}`. -/
public theorem exists_conjugate_sylow_le_rootAm_pred
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (n : Nat) (hn : 1 ≤ n)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (P : Sylow p H)
    (hpdeg : ¬ p ∣ n + 5) :
    ∃ P' : Sylow p H,
      (P' : Subgroup H) ≤
        centralRootAmPreimage (H := H) n (n + 4) (by omega) f := by
  let Q : Subgroup (alternatingGroup (Fin (n + 5))) :=
    (P : Subgroup H).map f
  have hQp : IsPGroup p Q := P.isPGroup'.map f
  have hpfin : ¬ p ∣ Nat.card (Fin (n + 5)) := by simpa using hpdeg
  obtain ⟨x, hx⟩ :=
    hQp.nonempty_fixed_point_of_prime_not_dvd_card (Fin (n + 5)) hpfin
  have hQfix : Q ≤
      MulAction.stabilizer (alternatingGroup (Fin (n + 5))) x := by
    intro q hq
    rw [MulAction.mem_stabilizer_iff]
    simpa using (MulAction.mem_fixedPoints.mp hx ⟨q, hq⟩)
  let : MulAction.IsPretransitive
      (alternatingGroup (Fin (n + 5))) (Fin (n + 5)) :=
    alternatingGroup.isPretransitive_of_three_le_card _ (by simp)
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq
    (alternatingGroup (Fin (n + 5))) x (Fin.last (n + 4))
  obtain ⟨h, hh⟩ := hsurj a
  let P' : Sylow p H := h • P
  refine ⟨P', ?_⟩
  intro y hy
  change f y ∈ rootAm n (n + 4) (by omega)
  rw [rootAm_pred_eq_stabilizer_last n hn,
    MulAction.mem_stabilizer_iff]
  let yP' : (h • P : Sylow p H) := ⟨y, hy⟩
  let zP : P := (P.equivSMul h).symm yP'
  let z : H := zP
  have hzP : z ∈ (P : Subgroup H) := zP.2
  have hyEq : (MulAut.conj h) z = y := by
    have heq := (P.equivSMul h).apply_symm_apply yP'
    exact congrArg Subtype.val heq
  have hfzQ : f z ∈ Q := by
    exact ⟨z, hzP, rfl⟩
  have hzfix : f z • x = x :=
    MulAction.mem_stabilizer_iff.mp (hQfix hfzQ)
  calc
    f y • Fin.last (n + 4) = f ((MulAut.conj h) z) • (a • x) := by
      rw [hyEq, ha]
    _ = (a * f z * a⁻¹) • (a • x) := by
      simp [MulAut.conj_apply, hh]
    _ = a • (f z • x) := by simp [mul_smul]
    _ = a • x := by rw [hzfix]
    _ = Fin.last (n + 4) := ha

/-- Point-stabilizer branch of A1 33.20.  If the central kernel is a
nontrivial `p`-group and the predecessor multiplier has no `p`-part, then
`p` must divide the permutation degree. -/
public theorem prime_dvd_degree_of_not_dvd_predecessor_multiplier
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    {p : Nat} [Fact p.Prime]
    (n : Nat) (hn : 1 ≤ n)
    (f : H →* alternatingGroup (Fin (n + 5)))
    (hsurj : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpker : p ∣ Nat.card f.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering ((n + 4) - 5)).toMonoidHom.ker) :
    p ∣ n + 5 := by
  by_contra hpdeg
  let P : Sylow p H := default
  obtain ⟨P', hP'root⟩ :=
    exists_conjugate_sylow_le_rootAm_pred n hn f hsurj P hpdeg
  have hKleP : f.ker ≤ (P' : Subgroup H) :=
    hkerp.le_sylow_of_normal P'
  let E := centralRootAmPreimage (H := H) n (n + 4) (by omega) f
  let r := centralRootAmPreimageProjection n (n + 4) (by omega) f
  let D := centralRootAmPreimageDerived n (n + 4) (by omega) f
  let K := r.ker
  have hcomp : K.IsComplement' D :=
    centralRootAmPreimageProjection_ker_isComplement'_derived_of_not_dvd_multiplier
      n (n + 4) (by omega) (by omega) f hsurj hker hkerp hpM
  let i : P' →* E :=
    (P' : Subgroup H).subtype.codRestrict E (fun x => hP'root x.2)
  let Kp : Subgroup P' := f.ker.comap (P' : Subgroup H).subtype
  let C : Subgroup P' := D.comap i
  have hKpFrattini : Kp ≤ frattini P' := by
    exact ker_comap_le_frattini_sylow P' f hker
  have hsup : C ⊔ Kp = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨kd, hkd⟩ := hcomp.2 (i x)
    let k : K := kd.1
    let d : D := kd.2
    have hkGlobal : ((k : E) : H) ∈ f.ker := by
      have hk := k.2
      change (k : E) ∈ r.ker at hk
      dsimp [r] at hk
      rw [centralRootAmPreimageProjection_ker_eq_comap] at hk
      exact hk
    let kp : P' := ⟨((k : E) : H), hKleP hkGlobal⟩
    have hkpKp : kp ∈ Kp := hkGlobal
    let dp : P' := kp⁻¹ * x
    have hidp : i dp = d := by
      apply Subtype.ext
      change ((k : E) : H)⁻¹ * (x : H) = ((d : E) : H)
      have hkdH := congrArg (fun z : E => (z : H)) hkd
      change ((k : E) : H) * ((d : E) : H) = (x : H) at hkdH
      rw [← hkdH]
      simp
    have hdpC : dp ∈ C := by
      change i dp ∈ D
      rw [hidp]
      exact d.2
    have hkpSup : kp ∈ C ⊔ Kp := Subgroup.mem_sup_right hkpKp
    have hdpSup : dp ∈ C ⊔ Kp := Subgroup.mem_sup_left hdpC
    have hxSup := Subgroup.mul_mem (C ⊔ Kp) hkpSup hdpSup
    simpa [dp] using hxSup
  have hCfrattini : C ⊔ frattini P' = ⊤ := by
    apply top_unique
    calc
      (⊤ : Subgroup P') = C ⊔ Kp := hsup.symm
      _ ≤ C ⊔ frattini P' := sup_le_sup le_rfl hKpFrattini
  have hCtop : C = ⊤ :=
    frattini_nongenerating (K := C) hCfrattini
  have hkerbot : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    let zp : P' := ⟨z, hKleP hz⟩
    have hzpC : zp ∈ C := by rw [hCtop]; trivial
    have hziD : i zp ∈ D := hzpC
    have hziK : i zp ∈ K := by
      change i zp ∈ r.ker
      dsimp [r]
      rw [centralRootAmPreimageProjection_ker_eq_comap]
      exact hz
    have hdisj := hcomp.disjoint
    rw [Subgroup.disjoint_def] at hdisj
    have hziOne : i zp = 1 := hdisj hziK hziD
    exact congrArg (fun y : E => (y : H)) hziOne
  rw [hkerbot, Subgroup.card_bot] at hpker
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hpker)

end GLS3.Chapter5.SchurPresentation

/- Source: PrimeSupportReduction.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-- Inductive prime-support reduction for alternating Schur multipliers.
If `p` divides the multiplier in degree `n+5` but not the multiplier of the
point stabilizer `A_{n+4}`, then `p` divides the degree `n+5` itself. -/
public theorem prime_dvd_degree_of_dvd_multiplier_of_not_dvd_predecessor
    {p : Nat} [Fact p.Prime]
    (n : Nat) (hn : 1 ≤ n)
    (hp : p ∣ Nat.card
      (alternatingFreeCentralCovering n).toMonoidHom.ker)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering ((n + 4) - 5)).toMonoidHom.ker) :
    p ∣ n + 5 := by
  let f := alternatingFreeCentralCovering n
  obtain ⟨X, hX, fbar, _hXker, hbarSurj, hbarCenter, hbarP, hpbar⟩ :=
    exists_pPrimary_quotient_central_extension
      f.toMonoidHom f.surjective f.ker_le_center hp
  let : X.Normal := hX
  exact prime_dvd_degree_of_not_dvd_predecessor_multiplier
    n hn fbar hbarSurj hbarCenter hbarP hpbar hpM

/-- Contrapositive induction form: away from degrees divisible by `p`, absence
of a `p`-part in the predecessor multiplier propagates to the next degree. -/
public theorem not_dvd_multiplier_of_not_dvd_degree_of_not_dvd_predecessor
    {p : Nat} [Fact p.Prime]
    (n : Nat) (hn : 1 ≤ n)
    (hpdeg : ¬ p ∣ n + 5)
    (hpM : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering ((n + 4) - 5)).toMonoidHom.ker) :
    ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering n).toMonoidHom.ker := by
  intro hp
  exact hpdeg
    (prime_dvd_degree_of_dvd_multiplier_of_not_dvd_predecessor n hn hp hpM)

end GLS3.Chapter5.SchurPresentation
/- END Theory.Reduction -/

/- BEGIN Theory.InvolutionCyclePermutationRootSupportEight -/
noncomputable section

namespace GLS3.Chapter5

open SchurPresentation.RootFourSubgroup
universe __ch5_InvolutionCyclePermutationRootSupportEight_u

/-- The standard root involution of the alternating group on the set of
nontrivial cycles swaps two pairs of cycles, hence moves eight points in the
original involution action. -/
public theorem involutionCyclePermutation_root_support_card
    {Ω : Type __ch5_InvolutionCyclePermutationRootSupportEight_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) (q : Nat)
    (eFin : x.cycleFactorsFinset ≃ Fin (q + 5)) :
    let e := theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two)
    let rootCycles : Equiv.Perm x.cycleFactorsFinset :=
      eFin.symm.permCongr (rho1 q)
    let l := e.symm rootCycles
    l.1.1.support.card = 8 := by
  dsimp only
  let hp : (orderOf x).Prime := by simpa [hx] using Nat.prime_two
  let e := theorem_5_2_2_d_3_a x hp
  let rootCycles : Equiv.Perm x.cycleFactorsFinset :=
    eFin.symm.permCongr (rho1 q)
  let l := e.symm rootCycles
  have hrootSupport : (rho1 q).support.card = 4 := by
    let h : 4 * 0 + 2 < q + 4 := by omega
    have heq : rho1 q = SchurPresentation.blockPerm q 0 h := by
      simp [rho1, SchurPresentation.blockPerm, p0, p1, p2, p3]
    rw [heq]
    exact SchurPresentation.blockPerm_support_card q 0 h
  have hcongrSupport : rootCycles.support.card = (rho1 q).support.card := by
    have hsupp : rootCycles.support =
        (rho1 q).support.map eFin.symm.toEmbedding := by
      ext y
      obtain ⟨z, rfl⟩ := eFin.symm.surjective y
      simp [rootCycles, Equiv.Perm.mem_support, Equiv.permCongr_apply]
    rw [hsupp, Finset.card_map]
  calc
    l.1.1.support.card = 2 * (e l).support.card :=
      involutionCyclePermutation_support_card_eq_two_mul x hx l
    _ = 2 * rootCycles.support.card := by rw [e.apply_symm_apply]
    _ = 2 * (rho1 q).support.card := by rw [hcongrSupport]
    _ = 8 := by rw [hrootSupport]

end GLS3.Chapter5
/- END Theory.InvolutionCyclePermutationRootSupportEight -/

/- BEGIN Theory.SignKernelDecompositionRotationOnly -/
noncomputable section

namespace GLS3.Chapter5

/-- If both the cycle-permuting complement and fixed-point factor lie in a
sign kernel, then the kernel is the product of the even rotation subgroup with
those two full factors. -/
public theorem signKernel_decomp_rotation_only
    {C : Type*} [Group C] (χ : C →* ℤˣ)
    (R L I : Subgroup C)
    (hLχ : L ≤ χ.ker)
    (hIχ : I ≤ χ.ker)
    (hLnorm : L ≤ Subgroup.normalizer R)
    (hIcomm : I ≤ Subgroup.centralizer
      ((R ⊔ L : Subgroup C) : Set C))
    (hsup : I ⊔ (R ⊔ L) = ⊤) :
    let Z := χ.ker
    let RZ := R.comap Z.subtype
    let LZ := L.comap Z.subtype
    let IZ := I.comap Z.subtype
    (RZ ⊔ LZ) ⊔ IZ = ⊤ := by
  dsimp only
  apply top_unique
  intro z _
  have hz : z.1 ∈ I ⊔ (R ⊔ L) := by rw [hsup]; trivial
  have hRLnormI : R ⊔ L ≤ Subgroup.normalizer I :=
    (Subgroup.le_centralizer_iff.mp hIcomm).trans
      (Subgroup.centralizer_le_normalizer (I : Set C))
  change z.1 ∈ (↑(I ⊔ (R ⊔ L)) : Set C) at hz
  rw [Subgroup.coe_mul_of_right_le_normalizer_left I (R ⊔ L) hRLnormI] at hz
  rcases hz with ⟨i, hi, w, hw, hiw⟩
  change w ∈ (↑(R ⊔ L) : Set C) at hw
  rw [Subgroup.coe_mul_of_right_le_normalizer_left R L hLnorm] at hw
  rcases hw with ⟨r, hr, l, hl, hrl⟩
  have hzval : z.1 = i * (r * l) :=
    hiw.symm.trans (congrArg (i * ·) hrl.symm)
  have hiχ : χ i = 1 := MonoidHom.mem_ker.mp (hIχ hi)
  have hlχ : χ l = 1 := MonoidHom.mem_ker.mp (hLχ hl)
  have hzχ : χ z.1 = 1 := MonoidHom.mem_ker.mp z.2
  have hrχ : χ r = 1 := by
    rw [hzval, map_mul, map_mul, hiχ, hlχ, mul_one, one_mul] at hzχ
    exact hzχ
  let iz : χ.ker := ⟨i, hIχ hi⟩
  let rz : χ.ker := ⟨r, MonoidHom.mem_ker.mpr hrχ⟩
  let lz : χ.ker := ⟨l, hLχ hl⟩
  have hprod : iz * (rz * lz) ∈
      (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
        I.comap (χ.ker).subtype := by
    apply Subgroup.mul_mem
    · exact (le_sup_right : I.comap (χ.ker).subtype ≤
        (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
          I.comap (χ.ker).subtype) hi
    · exact (le_sup_left :
        R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype ≤
          (R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) ⊔
            I.comap (χ.ker).subtype)
        ((R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype).mul_mem
          ((le_sup_left : R.comap (χ.ker).subtype ≤
            R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hr)
          ((le_sup_right : L.comap (χ.ker).subtype ≤
            R.comap (χ.ker).subtype ⊔ L.comap (χ.ker).subtype) hl))
  have heq : z = iz * (rz * lz) := Subtype.ext hzval
  rw [heq]
  exact hprod

end GLS3.Chapter5
/- END Theory.SignKernelDecompositionRotationOnly -/

/- BEGIN Theory.InvolutionCyclePermutationSignKernelEquiv -/
noncomputable section

namespace GLS3.Chapter5
universe __ch5_InvolutionCyclePermutationSignKernelEquiv_u

/-- For an involution, the full cycle-permuting complement lies in the even
centralizer, so its pullback to the sign kernel remains the full symmetric
group on the nontrivial cycles. -/
@[expose]
public noncomputable def involutionCyclePermutationSignKernelEquiv
    {Ω : Type __ch5_InvolutionCyclePermutationSignKernelEquiv_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2) :
    let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
    let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
    let Z := χ.ker
    (cyclePermutationSubgroup x).comap Z.subtype ≃*
      Equiv.Perm x.cycleFactorsFinset := by
  dsimp only
  let C := Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))
  let χ : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  have hLχ : cyclePermutationSubgroup x ≤ χ.ker := by
    intro l hl
    rw [MonoidHom.mem_ker]
    exact involutionCyclePermutation_sign x hx ⟨l, hl⟩
  exact (subgroupComapKernelEquivOfLe χ (cyclePermutationSubgroup x) hLχ).trans
    (theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two))

@[simp]
public theorem involutionCyclePermutationSignKernelEquiv_apply
    {Ω : Type __ch5_InvolutionCyclePermutationSignKernelEquiv_u} [Fintype Ω] [DecidableEq Ω]
    (x : Equiv.Perm Ω) (hx : orderOf x = 2)
    (z : (cyclePermutationSubgroup x).comap
      (Equiv.Perm.sign.comp
        (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))).subtype).ker.subtype) :
    involutionCyclePermutationSignKernelEquiv x hx z =
      (theorem_5_2_2_d_3_a x (by simpa [hx] using Nat.prime_two))
        ((subgroupComapKernelEquivOfLe
          (Equiv.Perm.sign.comp
            (Subgroup.centralizer ({x} : Set (Equiv.Perm Ω))).subtype)
          (cyclePermutationSubgroup x) (by
            intro l hl
            rw [MonoidHom.mem_ker]
            exact involutionCyclePermutation_sign x hx ⟨l, hl⟩)) z) := rfl

end GLS3.Chapter5
/- END Theory.InvolutionCyclePermutationSignKernelEquiv -/

/- BEGIN Theory.SubgroupComapKernelEquivRestrictKernel -/
namespace GLS3.Chapter5

/-- Pulling a subgroup back to a kernel is canonically equivalent to the
kernel of the restricted homomorphism. -/
public noncomputable def subgroupComapKernelEquivRestrictKernel
    {C M : Type*} [Group C] [Group M]
    (χ : C →* M) (H : Subgroup C) :
    H.comap χ.ker.subtype ≃* (χ.comp H.subtype).ker where
  toFun z := ⟨⟨z.1.1, z.2⟩, z.1.2⟩
  invFun h := ⟨⟨h.1.1, h.2⟩, h.1.2⟩
  left_inv z := by ext; rfl
  right_inv h := by ext; rfl
  map_mul' _ _ := rfl

end GLS3.Chapter5
/- END Theory.SubgroupComapKernelEquivRestrictKernel -/

/- BEGIN Theory.Imprimitive -/
universe __ch5_Imprimitive_u __ch5_Imprimitive_v

noncomputable section

/- Source: ImprimitiveWreathEmbedding.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation


/-! # The standard imprimitive alternating wreath embedding

This file realizes the semidirect product of alternating groups acting on a
block system as a subgroup of the alternating group on the product, and then
relabels the product as `Fin (p * d)`.
-/

@[expose]
public def permuteCoordinatesMulAut {I : Type __ch5_Imprimitive_u} (D : Type __ch5_Imprimitive_v) [Group D]
    (σ : Equiv.Perm I) : MulAut (I → D) where
  toFun x i := x (σ⁻¹ i)
  invFun x i := x (σ i)
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  map_mul' x y := rfl

@[expose]
public def permuteCoordinatesHom (I : Type __ch5_Imprimitive_u) (D : Type __ch5_Imprimitive_v) [Group D] :
    Equiv.Perm I →* MulAut (I → D) where
  toFun := permuteCoordinatesMulAut D
  map_one' := by
    ext x i
    rfl
  map_mul' σ τ := by
    ext x i
    rfl

@[simp]
public theorem permuteCoordinatesHom_apply {I : Type __ch5_Imprimitive_u} {D : Type __ch5_Imprimitive_v} [Group D]
    (σ : Equiv.Perm I) (x : I → D) (i : I) :
    permuteCoordinatesHom I D σ x i = x (σ⁻¹ i) := rfl

@[expose]
public def blockBasePermHom (I : Type __ch5_Imprimitive_u) (Λ : Type __ch5_Imprimitive_v) :
    (I → Equiv.Perm Λ) →* Equiv.Perm (I × Λ) where
  toFun h := Equiv.prodCongrRight h
  map_one' := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    rfl
  map_mul' h k := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    rfl

@[simp]
public theorem blockBasePermHom_apply (I : Type __ch5_Imprimitive_u) (Λ : Type __ch5_Imprimitive_v)
    (h : I → Equiv.Perm Λ) (i : I) (a : Λ) :
    blockBasePermHom I Λ h (i, a) = (i, h i a) := rfl

@[expose]
public def blockTopPermHom (I : Type __ch5_Imprimitive_u) (Λ : Type __ch5_Imprimitive_v) :
    Equiv.Perm I →* Equiv.Perm (I × Λ) where
  toFun σ := Equiv.prodCongrLeft (fun _ : Λ => σ)
  map_one' := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    rfl

@[simp]
public theorem blockTopPermHom_apply (I : Type __ch5_Imprimitive_u) (Λ : Type __ch5_Imprimitive_v)
    (σ : Equiv.Perm I) (i : I) (a : Λ) :
    blockTopPermHom I Λ σ (i, a) = (σ i, a) := rfl

@[simp]
public theorem blockTopPermHom_symm_apply (I : Type __ch5_Imprimitive_u) (Λ : Type __ch5_Imprimitive_v)
    (σ : Equiv.Perm I) (i : I) (a : Λ) :
    (blockTopPermHom I Λ σ).symm (i, a) = (σ⁻¹ i, a) := rfl

public theorem blockPerm_compatibility (I : Type __ch5_Imprimitive_u) (Λ : Type __ch5_Imprimitive_v)
    (σ : Equiv.Perm I) :
    (blockBasePermHom I Λ).comp
        ((permuteCoordinatesHom I (Equiv.Perm Λ)) σ).toMonoidHom =
      (MulAut.conj (blockTopPermHom I Λ σ)).toMonoidHom.comp
        (blockBasePermHom I Λ) := by
  apply MonoidHom.ext
  intro h
  apply Equiv.ext
  rintro ⟨i, a⟩
  simp [MonoidHom.comp_apply, MulAut.conj_apply, Equiv.Perm.mul_apply]

public def imprimitiveWreathPermHom (I : Type __ch5_Imprimitive_u) (Λ : Type __ch5_Imprimitive_v) :
    (I → Equiv.Perm Λ) ⋊[permuteCoordinatesHom I (Equiv.Perm Λ)] Equiv.Perm I →*
      Equiv.Perm (I × Λ) :=
  SemidirectProduct.lift (blockBasePermHom I Λ) (blockTopPermHom I Λ)
    (blockPerm_compatibility I Λ)

@[simp]
public theorem imprimitiveWreathPermHom_apply (I : Type __ch5_Imprimitive_u) (Λ : Type __ch5_Imprimitive_v)
    (x : (I → Equiv.Perm Λ) ⋊[permuteCoordinatesHom I (Equiv.Perm Λ)] Equiv.Perm I)
    (i : I) (a : Λ) :
    imprimitiveWreathPermHom I Λ x (i, a) =
      (x.right i, x.left (x.right i) a) := by
  simp [imprimitiveWreathPermHom, SemidirectProduct.lift,
    Equiv.Perm.mul_apply]

public theorem imprimitiveWreathPermHom_injective
    {I : Type __ch5_Imprimitive_u} {Λ : Type __ch5_Imprimitive_v} [Nonempty Λ] :
    Function.Injective (imprimitiveWreathPermHom I Λ) := by
  intro x y hxy
  let a : Λ := Classical.choice (inferInstance : Nonempty Λ)
  have hright : x.right = y.right := by
    apply Equiv.ext
    intro i
    have h := congrArg (fun e : Equiv.Perm (I × Λ) => e (i, a)) hxy
    exact congrArg Prod.fst h
  apply SemidirectProduct.ext
  · funext i
    apply Equiv.ext
    intro b
    have h := congrArg (fun e : Equiv.Perm (I × Λ) => e (y.right⁻¹ i, b)) hxy
    simpa [hright] using congrArg Prod.snd h
  · exact hright

public def alternatingBlockAction (p d : Nat) :
    alternatingGroup (Fin p) →*
      MulAut (Fin p → alternatingGroup (Fin d)) :=
  (permuteCoordinatesHom (Fin p) (alternatingGroup (Fin d))).comp
    (alternatingGroup (Fin p)).subtype

@[expose]
public def alternatingBlockBasePermHom (p d : Nat) :
    (Fin p → alternatingGroup (Fin d)) →* Equiv.Perm (Fin p × Fin d) where
  toFun h := blockBasePermHom (Fin p) (Fin d) (fun i => h i)
  map_one' := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    rfl
  map_mul' h k := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    rfl

@[simp]
public theorem alternatingBlockBasePermHom_apply (p d : Nat)
    (h : Fin p → alternatingGroup (Fin d)) (i : Fin p) (a : Fin d) :
    alternatingBlockBasePermHom p d h (i, a) = (i, (h i).1 a) := rfl

@[expose]
public def alternatingBlockTopPermHom (p d : Nat) :
    alternatingGroup (Fin p) →* Equiv.Perm (Fin p × Fin d) where
  toFun σ := blockTopPermHom (Fin p) (Fin d) σ
  map_one' := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    rfl
  map_mul' σ τ := by
    apply Equiv.ext
    rintro ⟨i, a⟩
    rfl

@[simp]
public theorem alternatingBlockTopPermHom_apply (p d : Nat)
    (σ : alternatingGroup (Fin p)) (i : Fin p) (a : Fin d) :
    alternatingBlockTopPermHom p d σ (i, a) = (σ.1 i, a) := rfl

@[simp]
public theorem alternatingBlockTopPermHom_symm_apply (p d : Nat)
    (σ : alternatingGroup (Fin p)) (i : Fin p) (a : Fin d) :
    (alternatingBlockTopPermHom p d σ).symm (i, a) = ((σ⁻¹).1 i, a) := rfl

public theorem alternatingBlockPerm_compatibility (p d : Nat)
    (σ : alternatingGroup (Fin p)) :
    (alternatingBlockBasePermHom p d).comp
        ((alternatingBlockAction p d) σ).toMonoidHom =
      (MulAut.conj (alternatingBlockTopPermHom p d σ)).toMonoidHom.comp
        (alternatingBlockBasePermHom p d) := by
  apply MonoidHom.ext
  intro h
  apply Equiv.ext
  rintro ⟨i, a⟩
  simp [alternatingBlockAction, MonoidHom.comp_apply, MulAut.conj_apply,
    Equiv.Perm.mul_apply]

@[expose]
public def alternatingImprimitivePermHom (p d : Nat) :
    (Fin p → alternatingGroup (Fin d)) ⋊[alternatingBlockAction p d]
        alternatingGroup (Fin p) →* Equiv.Perm (Fin p × Fin d) :=
  SemidirectProduct.lift (alternatingBlockBasePermHom p d)
    (alternatingBlockTopPermHom p d)
    (alternatingBlockPerm_compatibility p d)

@[simp]
public theorem alternatingImprimitivePermHom_apply (p d : Nat)
    (x : (Fin p → alternatingGroup (Fin d)) ⋊[alternatingBlockAction p d]
      alternatingGroup (Fin p)) (i : Fin p) (a : Fin d) :
    alternatingImprimitivePermHom p d x (i, a) =
      (x.right.1 i, (x.left (x.right.1 i)).1 a) := by
  simp [alternatingImprimitivePermHom, SemidirectProduct.lift,
    Equiv.Perm.mul_apply]

public theorem alternatingBlockBasePermHom_sign (p d : Nat)
    (h : Fin p → alternatingGroup (Fin d)) :
    Equiv.Perm.sign (alternatingBlockBasePermHom p d h) = 1 := by
  change Equiv.Perm.sign (Equiv.prodCongrRight (fun i => (h i : Equiv.Perm (Fin d)))) = 1
  rw [Equiv.Perm.sign_prodCongrRight]
  simp only [Equiv.Perm.mem_alternatingGroup.mp (h _).2, Finset.prod_const_one]

public theorem alternatingBlockTopPermHom_sign (p d : Nat)
    (σ : alternatingGroup (Fin p)) :
    Equiv.Perm.sign (alternatingBlockTopPermHom p d σ) = 1 := by
  change Equiv.Perm.sign
    (Equiv.prodCongrLeft (fun _ : Fin d => (σ : Equiv.Perm (Fin p)))) = 1
  rw [Equiv.Perm.sign_prodCongrLeft]
  simp only [Equiv.Perm.mem_alternatingGroup.mp σ.2, Finset.prod_const_one]

public theorem alternatingImprimitivePermHom_sign (p d : Nat)
    (x : (Fin p → alternatingGroup (Fin d)) ⋊[alternatingBlockAction p d]
      alternatingGroup (Fin p)) :
    Equiv.Perm.sign (alternatingImprimitivePermHom p d x) = 1 := by
  change Equiv.Perm.sign
    (alternatingBlockBasePermHom p d x.left *
      alternatingBlockTopPermHom p d x.right) = 1
  rw [map_mul, alternatingBlockBasePermHom_sign,
    alternatingBlockTopPermHom_sign, one_mul]

public def alternatingImprimitiveHom (p d : Nat) :
    (Fin p → alternatingGroup (Fin d)) ⋊[alternatingBlockAction p d]
        alternatingGroup (Fin p) →* alternatingGroup (Fin p × Fin d) :=
  (alternatingImprimitivePermHom p d).codRestrict _
    (fun x => Equiv.Perm.mem_alternatingGroup.mpr
      (alternatingImprimitivePermHom_sign p d x))

public theorem alternatingImprimitivePermHom_injective (p d : Nat) [Nonempty (Fin d)] :
    Function.Injective (alternatingImprimitivePermHom p d) := by
  intro x y hxy
  let a : Fin d := Classical.choice (inferInstance : Nonempty (Fin d))
  have hright : x.right = y.right := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    have h := congrArg (fun e : Equiv.Perm (Fin p × Fin d) => e (i, a)) hxy
    exact congrArg Prod.fst h
  apply SemidirectProduct.ext
  · funext i
    apply Subtype.ext
    apply Equiv.ext
    intro b
    have h := congrArg (fun e : Equiv.Perm (Fin p × Fin d) =>
      e ((y.right.1)⁻¹ i, b)) hxy
    simpa [hright] using congrArg Prod.snd h
  · exact hright

@[expose]
public def alternatingImprimitiveFinPermHom (p d : Nat) :
    (Fin p → alternatingGroup (Fin d)) ⋊[alternatingBlockAction p d]
        alternatingGroup (Fin p) →* Equiv.Perm (Fin (p * d)) :=
  (finProdFinEquiv.permCongrHom.toMonoidHom).comp
    (alternatingImprimitivePermHom p d)

public theorem alternatingImprimitiveFinPermHom_sign (p d : Nat)
    (x : (Fin p → alternatingGroup (Fin d)) ⋊[alternatingBlockAction p d]
      alternatingGroup (Fin p)) :
    Equiv.Perm.sign (alternatingImprimitiveFinPermHom p d x) = 1 := by
  simp [alternatingImprimitiveFinPermHom,
    alternatingImprimitivePermHom_sign]

@[expose]
public def alternatingImprimitiveFinHom (p d : Nat) :
    (Fin p → alternatingGroup (Fin d)) ⋊[alternatingBlockAction p d]
        alternatingGroup (Fin p) →* alternatingGroup (Fin (p * d)) :=
  (alternatingImprimitiveFinPermHom p d).codRestrict _
    (fun x => Equiv.Perm.mem_alternatingGroup.mpr
      (alternatingImprimitiveFinPermHom_sign p d x))

public theorem alternatingImprimitiveFinHom_injective (p d : Nat) [Nonempty (Fin d)] :
    Function.Injective (alternatingImprimitiveFinHom p d) := by
  intro x y h
  apply alternatingImprimitivePermHom_injective p d
  apply finProdFinEquiv.permCongrHom.injective
  exact congrArg Subtype.val h

end GLS3.Chapter5.SchurPresentation

/- Source: ImprimitiveSylow.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! # Sylow subgroups in the standard imprimitive alternating subgroup

For an odd prime `p` and a positive power `p ^ s`, the standard embedding of
`(A_(p^s))^p ⋊ A_p` in `A_(p^(s+1))` contains a Sylow `p`-subgroup.  The
proof compares the `p`-parts of the two group orders using Legendre's formula.
-/

/-- Away from the prime two, the `p`-part of the alternating-group order is
the `p`-part of the corresponding factorial. -/
public theorem alternating_card_factorization_eq_factorial
    (p n : Nat) (hp5 : 5 ≤ p) (hn : 2 ≤ n) :
    (Nat.card (alternatingGroup (Fin n))).factorization p =
      n.factorial.factorization p := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have hp2 : ¬ p ∣ 2 := Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have h := congrArg (fun m : Nat => m.factorization p)
    (two_mul_nat_card_alternatingGroup (α := Fin n))
  rw [Nat.factorization_mul (by decide) Nat.card_pos.ne'] at h
  simp only [Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hp2, zero_add,
    Nat.card_perm, Nat.card_fin] at h
  exact h

/-- The valuation identity making the imprimitive subgroup have the full
`p`-part when the block size is a power of `p`. -/
public theorem factorial_power_factorization_relation
    (p s : Nat) (hp : p.Prime) :
    p * ((p ^ s).factorial.factorization p) + 1 =
      ((p ^ s).factorial.factorization p) + p ^ s := by
  rw [← Nat.multiplicity_eq_factorization hp (p ^ s).factorial_ne_zero,
    hp.multiplicity_factorial_pow]
  have hgeom :
      (∑ i ∈ Finset.range s, p ^ i) * (p - 1) + 1 = p ^ s := by
    simpa only [Nat.sub_add_cancel hp.one_le] using
      (geom_sum_mul_add (p - 1) s)
  calc
    p * (∑ i ∈ Finset.range s, p ^ i) + 1 =
        ((p - 1) + 1) * (∑ i ∈ Finset.range s, p ^ i) + 1 := by
          rw [Nat.sub_add_cancel hp.one_le]
    _ = (∑ i ∈ Finset.range s, p ^ i) +
        ((∑ i ∈ Finset.range s, p ^ i) * (p - 1) + 1) := by ring
    _ = (∑ i ∈ Finset.range s, p ^ i) + p ^ s := by rw [hgeom]

/-- The domain of the standard alternating imprimitive embedding. -/
public abbrev alternatingImprimitiveGroup (p d : Nat) :=
  (Fin p → alternatingGroup (Fin d)) ⋊[alternatingBlockAction p d]
    alternatingGroup (Fin p)

public theorem alternatingImprimitiveGroup_card (p d : Nat) :
    Nat.card (alternatingImprimitiveGroup p d) =
      Nat.card (alternatingGroup (Fin d)) ^ p *
        Nat.card (alternatingGroup (Fin p)) := by
  rw [SemidirectProduct.card, Nat.card_fun, Nat.card_fin]

/-- For a positive exponent, the standard imprimitive subgroup and the
ambient alternating group have the same `p`-part. -/
public theorem alternatingImprimitiveGroup_factorization_eq_ambient
    (p s : Nat) (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 0 < s) :
    (Nat.card (alternatingImprimitiveGroup p (p ^ s))).factorization p =
      (Nat.card (alternatingGroup (Fin (p * p ^ s)))).factorization p := by
  have hps : p ≤ p ^ s := by
    simpa only [pow_one] using (pow_le_pow_right₀ hp.one_le hs)
  have hd2 : 2 ≤ p ^ s := hp.two_le.trans hps
  have hpd2 : 2 ≤ p * p ^ s :=
    hp.two_le.trans (Nat.le_mul_of_pos_right p (pow_pos hp.pos s))
  have hpfact : p.factorial.factorization p = 1 := by
    simpa using (Nat.factorization_factorial_mul (n := 1) hp)
  rw [alternatingImprimitiveGroup_card,
    Nat.factorization_mul (pow_ne_zero _ Nat.card_pos.ne') Nat.card_pos.ne',
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, nsmul_eq_mul,
    alternating_card_factorization_eq_factorial p (p ^ s) hp5 hd2,
    alternating_card_factorization_eq_factorial p p hp5 hp.two_le,
    alternating_card_factorization_eq_factorial p (p * p ^ s) hp5 hpd2,
    hpfact, Nat.factorization_factorial_mul hp]
  exact factorial_power_factorization_relation p s hp

/-- The image of the standard imprimitive embedding contains a Sylow
`p`-subgroup of the ambient alternating group. -/
public theorem exists_sylow_le_alternatingImprimitiveFinHom_range
    (p s : Nat) (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 0 < s) :
    ∃ P : Sylow p (alternatingGroup (Fin (p * p ^ s))),
      (P : Subgroup (alternatingGroup (Fin (p * p ^ s)))) ≤
        (alternatingImprimitiveFinHom p (p ^ s)).range := by
  let : Fact p.Prime := ⟨hp⟩
  let : Nonempty (Fin (p ^ s)) := ⟨⟨0, pow_pos hp.pos s⟩⟩
  let : Finite (alternatingImprimitiveGroup p (p ^ s)) :=
    Finite.of_equiv
      ((Fin p → alternatingGroup (Fin (p ^ s))) × alternatingGroup (Fin p))
      (SemidirectProduct.equivProd
        (φ := alternatingBlockAction p (p ^ s))).symm
  let Q : Sylow p (alternatingImprimitiveGroup p (p ^ s)) :=
    Classical.choice Sylow.nonempty
  let H : Subgroup (alternatingGroup (Fin (p * p ^ s))) :=
    (Q : Subgroup (alternatingImprimitiveGroup p (p ^ s))).map
      (alternatingImprimitiveFinHom p (p ^ s))
  have hinj : Function.Injective (alternatingImprimitiveFinHom p (p ^ s)) :=
    alternatingImprimitiveFinHom_injective p (p ^ s)
  have hHcard : Nat.card H =
      p ^ (Nat.card (alternatingGroup (Fin (p * p ^ s)))).factorization p := by
    change Nat.card ((Q : Subgroup (alternatingImprimitiveGroup p (p ^ s))).map
      (alternatingImprimitiveFinHom p (p ^ s))) = _
    rw [Subgroup.card_map_of_injective hinj, Sylow.card_eq_multiplicity Q,
      alternatingImprimitiveGroup_factorization_eq_ambient p s hp hp5 hs]
  let P : Sylow p (alternatingGroup (Fin (p * p ^ s))) := Sylow.ofCard H hHcard
  refine ⟨P, ?_⟩
  change H ≤ (alternatingImprimitiveFinHom p (p ^ s)).range
  exact Subgroup.map_le_range _ _

/-- Version with a separately named block degree, convenient for inductive
arguments whose degree is known to equal a prime power. -/
public theorem exists_sylow_le_alternatingImprimitiveFinHom_range_of_eq_prime_pow
    (p d s : Nat) (hp : p.Prime) (hp5 : 5 ≤ p) (hs : 0 < s)
    (hd : d = p ^ s) :
    ∃ P : Sylow p (alternatingGroup (Fin (p * d))),
      (P : Subgroup (alternatingGroup (Fin (p * d)))) ≤
        (alternatingImprimitiveFinHom p d).range := by
  subst d
  exact exists_sylow_le_alternatingImprimitiveFinHom_range p s hp hp5 hs

end GLS3.Chapter5.SchurPresentation

/- Source: ImprimitiveSubextension.lean -/

set_option maxHeartbeats 800000


namespace GLS3.Chapter5.SchurPresentation

/-! # Central extensions restricted to the imprimitive subgroup

This file restricts a central extension of an alternating group to the full
preimage of the standard imprimitive subgroup.  The projection is transported
across the injective wreath embedding, so the semidirect-product splitting
theorem applies directly.  Sylow containment then feeds the resulting
complement into the generic A1 33.11 Frattini contradiction.
-/

/-- Full preimage of the standard imprimitive alternating subgroup. -/
public abbrev alternatingImprimitivePreimage
    {H : Type*} [Group H] (p d : Nat)
    (f : H →* alternatingGroup (Fin (p * d))) : Subgroup H :=
  (alternatingImprimitiveFinHom p d).range.comap f

/-- Projection of the full preimage to the abstract alternating wreath
semidirect product. -/
@[expose]
public def alternatingImprimitivePreimageProjection
    {H : Type*} [Group H] (p d : Nat) [Nonempty (Fin d)]
    (f : H →* alternatingGroup (Fin (p * d))) :
    alternatingImprimitivePreimage p d f →* alternatingImprimitiveGroup p d :=
  let i := alternatingImprimitiveFinHom p d
  let e := MonoidHom.ofInjective (alternatingImprimitiveFinHom_injective p d)
  e.symm.toMonoidHom.comp
    ((f.comp (alternatingImprimitivePreimage p d f).subtype).codRestrict
      i.range (fun x => x.2))

public theorem alternatingImprimitivePreimageProjection_surjective
    {H : Type*} [Group H] (p d : Nat) [Nonempty (Fin d)]
    (f : H →* alternatingGroup (Fin (p * d)))
    (hf : Function.Surjective f) :
    Function.Surjective (alternatingImprimitivePreimageProjection p d f) := by
  intro y
  let i := alternatingImprimitiveFinHom p d
  let e := MonoidHom.ofInjective (alternatingImprimitiveFinHom_injective p d)
  obtain ⟨x, hx⟩ := hf (i y)
  have hxE : x ∈ alternatingImprimitivePreimage p d f := ⟨y, hx.symm⟩
  let xE : alternatingImprimitivePreimage p d f := ⟨x, hxE⟩
  refine ⟨xE, ?_⟩
  change e.symm ⟨f x, hxE⟩ = y
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact hx

/-- The restricted kernel is the comap of the global kernel. -/
public theorem alternatingImprimitivePreimageProjection_ker_eq_comap
    {H : Type*} [Group H] (p d : Nat) [Nonempty (Fin d)]
    (f : H →* alternatingGroup (Fin (p * d))) :
    (alternatingImprimitivePreimageProjection p d f).ker =
      f.ker.comap (alternatingImprimitivePreimage p d f).subtype := by
  let i := alternatingImprimitiveFinHom p d
  let e := MonoidHom.ofInjective (alternatingImprimitiveFinHom_injective p d)
  let r0 := (f.comp (alternatingImprimitivePreimage p d f).subtype).codRestrict
    i.range (fun x => x.2)
  calc
    (alternatingImprimitivePreimageProjection p d f).ker = r0.ker :=
      MonoidHom.ker_comp_of_injective r0 e.symm.toMonoidHom e.symm.injective
    _ = f.ker.comap (alternatingImprimitivePreimage p d f).subtype := by
      ext x
      dsimp [r0]
      constructor
      · intro hx
        have hx0 := MonoidHom.mem_ker.mp hx
        exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx0)
      · intro hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hx

/-- Centrality of the global kernel descends to the restricted extension. -/
public theorem alternatingImprimitivePreimageProjection_ker_le_center
    {H : Type*} [Group H] (p d : Nat) [Nonempty (Fin d)]
    (f : H →* alternatingGroup (Fin (p * d)))
    (hker : f.ker ≤ Subgroup.center H) :
    (alternatingImprimitivePreimageProjection p d f).ker ≤
      Subgroup.center (alternatingImprimitivePreimage p d f) := by
  rw [alternatingImprimitivePreimageProjection_ker_eq_comap]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hx) y.1

set_option backward.isDefEq.respectTransparency false in
/-- The imprimitive subextension splits when the base and top alternating
multipliers have no contribution at the kernel prime. -/
public theorem exists_alternatingImprimitivePreimage_section_isComplement'
    {H : Type} [Group H] [Finite H]
    {p : Nat} [Fact p.Prime]
    (qBase qTop : Nat)
    (f : H →* alternatingGroup
      (Fin ((qTop + 5) * (qBase + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup p f.ker)
    (hpBase : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qBase).toMonoidHom.ker)
    (hpTop : ¬ p ∣ Nat.card
      (alternatingFreeCentralCovering qTop).toMonoidHom.ker) :
    ∃ s : alternatingImprimitiveGroup (qTop + 5) (qBase + 5) →*
        alternatingImprimitivePreimage (qTop + 5) (qBase + 5) f,
      (alternatingImprimitivePreimageProjection
        (qTop + 5) (qBase + 5) f).comp s = MonoidHom.id _ ∧
      (alternatingImprimitivePreimageProjection
        (qTop + 5) (qBase + 5) f).ker.IsComplement' s.range := by
  let r := alternatingImprimitivePreimageProjection
    (qTop + 5) (qBase + 5) f
  have hrSurj : Function.Surjective r :=
    alternatingImprimitivePreimageProjection_surjective _ _ f hf
  have hrCenter : r.ker ≤ Subgroup.center
      (alternatingImprimitivePreimage (qTop + 5) (qBase + 5) f) :=
    alternatingImprimitivePreimageProjection_ker_le_center _ _ f hker
  have hrP : IsPGroup p r.ker := by
    rw [alternatingImprimitivePreimageProjection_ker_eq_comap]
    exact hkerp.comap_subtype
  exact
    exists_alternatingPowerSemidirect_section_isComplement'_of_not_dvd_multipliers
      qBase qTop (qTop + 5)
      (alternatingBlockAction (qTop + 5) (qBase + 5))
      r hrSurj hrCenter hrP hpBase hpTop

/-- Case II of the odd-prime minimal-counterexample argument: if the degree
is a positive power of the kernel prime, the imprimitive Sylow subgroup and
the split restricted extension force the global kernel to vanish. -/
public theorem kernel_eq_bot_of_alternatingImprimitive_primePower
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (qBase qTop s : Nat)
    (hp : (qTop + 5).Prime) (hs : 0 < s)
    (hpow : qBase + 5 = (qTop + 5) ^ s)
    (f : H →* alternatingGroup
      (Fin ((qTop + 5) * (qBase + 5))))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup (qTop + 5) f.ker)
    (hpBase : ¬ (qTop + 5) ∣ Nat.card
      (alternatingFreeCentralCovering qBase).toMonoidHom.ker)
    (hpTop : ¬ (qTop + 5) ∣ Nat.card
      (alternatingFreeCentralCovering qTop).toMonoidHom.ker) :
    f.ker = ⊥ := by
  let : Fact (qTop + 5).Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ :
      ∃ S : Sylow (qTop + 5) (alternatingGroup
          (Fin ((qTop + 5) * (qBase + 5)))),
        (S : Subgroup _) ≤
          (alternatingImprimitiveFinHom (qTop + 5) (qBase + 5)).range := by
    exact exists_sylow_le_alternatingImprimitiveFinHom_range_of_eq_prime_pow
      (qTop + 5) (qBase + 5) s hp (by omega) hs hpow
  have hSrange : (S : Subgroup _) ≤ f.range := by
    intro x hx
    exact ⟨Classical.choose (hf x), Classical.choose_spec (hf x)⟩
  let P : Sylow (qTop + 5) H := S.comapOfKerIsPGroup f hkerp hSrange
  let E := alternatingImprimitivePreimage (qTop + 5) (qBase + 5) f
  have hPE : (P : Subgroup H) ≤ E := by
    intro x hx
    change f x ∈ (alternatingImprimitiveFinHom
      (qTop + 5) (qBase + 5)).range
    apply hS
    exact hx
  obtain ⟨t, -, hcomp⟩ :=
    exists_alternatingImprimitivePreimage_section_isComplement'
      qBase qTop f hf hker hkerp hpBase hpTop
  exact kernel_eq_bot_of_sylow_le_subgroup_of_kernel_comap_isComplement'
    f hker hkerp P E hPE t.range (by
      rw [← alternatingImprimitivePreimageProjection_ker_eq_comap]
      exact hcomp)

/-- Relabeled form of the prime-power endpoint for an ambient degree known to
equal the imprimitive product degree. -/
public theorem kernel_eq_bot_of_alternatingImprimitive_primePower_degree
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (qBase qTop s m : Nat)
    (hp : (qTop + 5).Prime) (hs : 0 < s)
    (hpow : qBase + 5 = (qTop + 5) ^ s)
    (hm : m = (qTop + 5) * (qBase + 5))
    (f : H →* alternatingGroup (Fin m))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hkerp : IsPGroup (qTop + 5) f.ker)
    (hpBase : ¬ (qTop + 5) ∣ Nat.card
      (alternatingFreeCentralCovering qBase).toMonoidHom.ker)
    (hpTop : ¬ (qTop + 5) ∣ Nat.card
      (alternatingFreeCentralCovering qTop).toMonoidHom.ker) :
    f.ker = ⊥ := by
  let e : Fin m ≃ Fin ((qTop + 5) * (qBase + 5)) := finCongr hm
  let f' : H →* alternatingGroup (Fin ((qTop + 5) * (qBase + 5))) :=
    e.altCongrHom.toMonoidHom.comp f
  have hfker : f'.ker = f.ker :=
    MonoidHom.ker_comp_of_injective f e.altCongrHom.toMonoidHom
      e.altCongrHom.injective
  have hf'surj : Function.Surjective f' := e.altCongrHom.surjective.comp hf
  have hf'center : f'.ker ≤ Subgroup.center H := by
    rw [hfker]
    exact hker
  have hf'p : IsPGroup (qTop + 5) f'.ker := by
    rw [hfker]
    exact hkerp
  have hbot := kernel_eq_bot_of_alternatingImprimitive_primePower
    qBase qTop s hp hs hpow f' hf'surj hf'center hf'p hpBase hpTop
  rwa [hfker] at hbot

end GLS3.Chapter5.SchurPresentation
/- END Theory.Imprimitive -/

/- BEGIN Theory.ThreeCycleBlockSubextension -/
set_option maxHeartbeats 800000

noncomputable section

namespace GLS3.Chapter5.SchurPresentation

open RootAm
open scoped commutatorElement Pointwise

private def __ch5_ThreeCycleBlockSubextension_rootThreeCycle : alternatingGroup (Fin 5) :=
  alternatingSuzukiGenerator 0 0

@[expose]
public def a3Generator : alternatingGroup (Fin 3) :=
  ⟨Equiv.swap (0 : Fin 3) (1 : Fin 3) *
      Equiv.swap (0 : Fin 3) (2 : Fin 3), by
    rw [Equiv.Perm.mem_alternatingGroup, map_mul,
      Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 1 by decide),
      Equiv.Perm.sign_swap (show (0 : Fin 3) ≠ 2 by decide)]
    simp⟩

private theorem __ch5_ThreeCycleBlockSubextension_a3Generator_isThreeCycle :
    Equiv.Perm.IsThreeCycle (a3Generator : Equiv.Perm (Fin 3)) := by
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same
    (a := (0 : Fin 3)) (b := (1 : Fin 3)) (c := (2 : Fin 3))
    (show (0 : Fin 3) ≠ 1 by decide)
    (show (0 : Fin 3) ≠ 2 by decide)
    (show (1 : Fin 3) ≠ 2 by decide)

private theorem __ch5_ThreeCycleBlockSubextension_blockA3Generator_isThreeCycle (d : Nat) :
    Equiv.Perm.IsThreeCycle
      ((alternatingProdBlockHom 3 d (a3Generator, 1) :
      alternatingGroup (Fin (3 + d))) : Equiv.Perm (Fin (3 + d))) := by
  let a : Fin (3 + d) := Fin.castAdd d 0
  let b : Fin (3 + d) := Fin.castAdd d 1
  let c : Fin (3 + d) := Fin.castAdd d 2
  rw [show ((alternatingProdBlockHom 3 d (a3Generator, 1) :
      alternatingGroup (Fin (3 + d))) : Equiv.Perm (Fin (3 + d))) =
      Equiv.swap a b * Equiv.swap a c by
    rw [coe_alternatingProdBlockHom_apply, permProdBlockHom_apply]
    apply Equiv.ext
    intro i
    rw [← finSumFinEquiv.apply_symm_apply i]
    generalize finSumFinEquiv.symm i = z
    rcases z with j | j
    · fin_cases j <;>
        simp [a3Generator, a, b, c, Equiv.Perm.mul_apply,
          Equiv.swap_apply_def]
    · have h0 : Fin.natAdd 3 j ≠ a := by
        intro h
        have := congrArg Fin.val h
        simp [a] at this
      have h1 : Fin.natAdd 3 j ≠ b := by
        intro h
        have := congrArg Fin.val h
        simp [b] at this
        omega
      have h2 : Fin.natAdd 3 j ≠ c := by
        intro h
        have := congrArg Fin.val h
        simp [c] at this
        omega
      simp [a3Generator, a, b, c, Equiv.Perm.mul_apply,
        Equiv.swap_apply_def, h0, h1, h2]]
  exact Equiv.Perm.isThreeCycle_swap_mul_swap_same (a := a) (b := b) (c := c)
    (by intro h; have hv := congrArg Fin.val h; norm_num [a, b] at hv)
    (by intro h; have hv := congrArg Fin.val h; norm_num [a, c] at hv)
    (by intro h; have hv := congrArg Fin.val h; norm_num [b, c] at hv)

private theorem __ch5_ThreeCycleBlockSubextension_isThreeCycle_permCongr
    {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α)
    (hσ : Equiv.Perm.IsThreeCycle σ) :
    Equiv.Perm.IsThreeCycle (e.permCongr σ) := by
  rw [← card_support_eq_three_iff]
  have hsupp : (e.permCongr σ).support = σ.support.map e.toEmbedding := by
    ext x
    simp [Equiv.Perm.mem_support, Equiv.permCongr_apply]
    constructor
    · intro h hEq
      apply h
      rw [hEq, e.apply_symm_apply]
    · intro h hEq
      apply h
      apply e.injective
      simpa using hEq
  rw [hsupp, Finset.card_map, hσ.card_support]

public theorem exists_cyclic_section_of_order_three
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    (g : A) (hcardA : Nat.card A = 3) (hg : orderOf g = 3)
    (y : H) (hy : orderOf y = 3) :
    ∃ s : A →* H, s g = y := by
  have hcardZG : Nat.card (Subgroup.zpowers g) = Nat.card A := by
    rw [Nat.card_zpowers, hg, hcardA]
  have htopG : Subgroup.zpowers g = ⊤ :=
    (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers g)).mp hcardZG
  have hgenG : ∀ x : A, x ∈ Subgroup.zpowers g := fun x => by
    rw [htopG]
    trivial
  let Y := Subgroup.zpowers y
  let yg : Y := ⟨y, Subgroup.mem_zpowers y⟩
  have hordyg : orderOf yg = 3 :=
    (Subgroup.orderOf_coe yg).symm.trans hy
  have hcardY : Nat.card Y = 3 := by
    exact (Nat.card_zpowers y).trans hy
  have hcardZYG : Nat.card (Subgroup.zpowers yg) = Nat.card Y := by
    rw [Nat.card_zpowers, hordyg, hcardY]
  have htopY : Subgroup.zpowers yg = ⊤ :=
    (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers yg)).mp hcardZYG
  have hgenY : ∀ z : Y, z ∈ Subgroup.zpowers yg := fun z => by
    rw [htopY]
    trivial
  let eG : Multiplicative (ZMod 3) ≃* A :=
    zmodMulEquivOfGenerator hgenG hcardA
  let eY : Multiplicative (ZMod 3) ≃* Y :=
    zmodMulEquivOfGenerator hgenY hcardY
  let s : A →* H := Y.subtype.comp (eG.symm.trans eY).toMonoidHom
  refine ⟨s, ?_⟩
  change ((eY (eG.symm g) : Y) : H) = y
  rw [zmodMulEquivOfGenerator_symm_apply_generator,
    zmodMulEquivOfGenerator_apply_ofAdd_one]

public theorem a3Generator_orderOf : orderOf a3Generator = 3 := by
  rw [← Subgroup.orderOf_coe]
  exact __ch5_ThreeCycleBlockSubextension_a3Generator_isThreeCycle.orderOf

public theorem a3_card : Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  norm_num [Nat.factorial]

public theorem a3Generator_zpowers_eq_top :
    Subgroup.zpowers a3Generator = ⊤ := by
  apply (Subgroup.card_eq_iff_eq_top (Subgroup.zpowers a3Generator)).mp
  rw [Nat.card_zpowers, a3Generator_orderOf, a3_card]

private theorem __ch5_ThreeCycleBlockSubextension_map_eq_one_of_isPerfect_to_commGroup
    {A C : Type*} [Group A] [CommGroup C] [Group.IsPerfect A]
    (f : A →* C) (a : A) : f a = 1 := by
  apply MonoidHom.mem_ker.mp
  exact Abelianization.commutator_subset_ker f
    (Group.IsPerfect.mem_commutator (g := a))

private theorem __ch5_ThreeCycleBlockSubextension_commutatorElement_eq_one_of_left_perfect_of_mem_center
    {A H : Type*} [Group A] [Group H] [Group.IsPerfect A]
    (s : A →* H) (y : H)
    (hc : ∀ a : A, ⁅s a, y⁆ ∈ Subgroup.center H)
    (a : A) : ⁅s a, y⁆ = 1 := by
  let : CommGroup (Subgroup.center H) := {
    mul_comm := fun x z => Subtype.ext
      (Subgroup.mem_center_iff.mp x.2 z.1).symm }
  let φ : A →* Subgroup.center H := {
    toFun := fun x => ⟨⁅s x, y⁆, hc x⟩
    map_one' := by
      apply Subtype.ext
      simp
    map_mul' := by
      intro a₁ a₂
      apply Subtype.ext
      change ⁅s (a₁ * a₂), y⁆ = ⁅s a₁, y⁆ * ⁅s a₂, y⁆
      rw [map_mul, commutatorElement_mul_left_eq_conj_mul]
      have hc₂ := hc a₂
      have hconj : s a₁ * ⁅s a₂, y⁆ * (s a₁)⁻¹ = ⁅s a₂, y⁆ := by
        have hcomm := Subgroup.mem_center_iff.mp hc₂ (s a₁)
        rw [hcomm]
        simp
      rw [hconj]
      exact (Subgroup.mem_center_iff.mp hc₂ ⁅s a₁, y⁆).symm
  }
  exact congrArg Subtype.val
    (__ch5_ThreeCycleBlockSubextension_map_eq_one_of_isPerfect_to_commGroup φ a)

private theorem __ch5_ThreeCycleBlockSubextension_rootThreeCycle_global_isThreeCycle (n : Nat) :
    Equiv.Perm.IsThreeCycle
      ((tailAltHom n 5 (by omega) __ch5_ThreeCycleBlockSubextension_rootThreeCycle :
        alternatingGroup (Fin (n + 5))) : Equiv.Perm (Fin (n + 5))) := by
  rw [show ((tailAltHom n 5 (by omega) __ch5_ThreeCycleBlockSubextension_rootThreeCycle :
      alternatingGroup (Fin (n + 5))) : Equiv.Perm (Fin (n + 5))) =
      adjacentSwap n 0 * adjacentSwap n 1 by
    change tailPermHom n 5 (by omega)
        (alternatingSuzukiGenerator 0 0 : Equiv.Perm (Fin 5)) = _
    rw [alternatingSuzukiGenerator_val, map_mul,
      tailPermHom_adjacentSwap n 5 (by omega),
      tailPermHom_adjacentSwap n 5 (by omega)]
    rfl]
  exact adjacentSwap_mul_adjacentSwap_isThreeCycle n 0

/-- Every three-cycle has an order-three lift through a finite central
extension with 3-primary kernel. This is the first assertion of A1 33.18 in
a conjugacy-invariant form. -/
public theorem exists_threeCycle_lift_order_three
    {H : Type*} [Group H] [Finite H]
    (n : Nat) (f : H →* alternatingGroup (Fin (n + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (a : alternatingGroup (Fin (n + 5)))
    (ha : Equiv.Perm.IsThreeCycle (a : Equiv.Perm (Fin (n + 5)))) :
    ∃ y : H, f y = a ∧ orderOf y = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a0 : alternatingGroup (Fin 5) := __ch5_ThreeCycleBlockSubextension_rootThreeCycle
  obtain ⟨y0, hy0, hord0⟩ :=
    exists_rootA5PreimageDerived_lift_orderOf_eq_of_isPGroup
      (p := 3) (by omega) n f hf hker hker3 a0
  let y0H : H := ((y0 : rootA5Preimage n f) : H)
  let aN : alternatingGroup (Fin (n + 5)) :=
    tailAltHom n 5 (by omega) a0
  have hfy0 : f y0H = aN := by
    change (rootA5Equiv n).symm
      ⟨f y0H, (y0 : rootA5Preimage n f).2⟩ = a0 at hy0
    have hy := congrArg (rootA5Equiv n) hy0
    rw [(rootA5Equiv n).apply_symm_apply] at hy
    exact congrArg Subtype.val hy
  have haN : Equiv.Perm.IsThreeCycle
      (aN : Equiv.Perm (Fin (n + 5))) :=
    __ch5_ThreeCycleBlockSubextension_rootThreeCycle_global_isThreeCycle n
  have hordA0 : orderOf a0 = 3 := by
    change orderOf (alternatingSuzukiGenerator 0 0) = 3
    rw [← Subgroup.orderOf_coe]
    exact (adjacentSwap_mul_adjacentSwap_isThreeCycle 0 0).orderOf
  have hordY0 : orderOf y0H = 3 := by
    calc
      orderOf y0H = orderOf y0 := by
        exact (Subgroup.orderOf_coe (y0 : rootA5Preimage n f)).trans
          (Subgroup.orderOf_coe y0)
      _ = orderOf a0 := hord0
      _ = 3 := hordA0
  obtain ⟨c, hc⟩ := alternatingGroup.isThreeCycle_isConj
    (α := Fin (n + 5)) (by simp) haN ha
  obtain ⟨x, hx⟩ := hf c
  refine ⟨x * y0H * x⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv, hx, hfy0]
    rw [hc]
    simp
  · have hord := orderOf_injective (MulAut.conj x).toMonoidHom
        (MulAut.conj x).injective y0H
    change orderOf (x * y0H * x⁻¹) = orderOf y0H at hord
    exact hord.trans hordY0

/-- The standard `A_3 × A_(q+5)` block subgroup, relabeled to degree
`(q+3)+5` so that the root-`A_5` induction API applies definitionally. -/
public def threeBlockHom (q : Nat) :
    alternatingGroup (Fin 3) × alternatingGroup (Fin (q + 5)) →*
      alternatingGroup (Fin ((q + 3) + 5)) :=
  ((finCongr (by omega : 3 + (q + 5) = (q + 3) + 5)).altCongrHom).toMonoidHom.comp
    (alternatingProdBlockHom 3 (q + 5))

public theorem threeBlockHom_injective (q : Nat) :
    Function.Injective (threeBlockHom q) := by
  exact (finCongr (by omega : 3 + (q + 5) = (q + 3) + 5)).altCongrHom.injective.comp
    (alternatingProdBlockHom_injective 3 (q + 5))

private theorem __ch5_ThreeCycleBlockSubextension_threeBlockGenerator_isThreeCycle (q : Nat) :
    Equiv.Perm.IsThreeCycle
      ((threeBlockHom q (a3Generator, 1) :
        alternatingGroup (Fin ((q + 3) + 5))) :
          Equiv.Perm (Fin ((q + 3) + 5))) := by
  exact __ch5_ThreeCycleBlockSubextension_isThreeCycle_permCongr
    (finCongr (by omega : 3 + (q + 5) = (q + 3) + 5))
    _ (__ch5_ThreeCycleBlockSubextension_blockA3Generator_isThreeCycle (q + 5))

/-- The full preimage of the standard three-point block subgroup. -/
public abbrev threeBlockPreimage
    {H : Type*} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5))) : Subgroup H :=
  (threeBlockHom q).range.comap f

/-- Projection from the three-point block preimage to `A_3 × A_(q+5)`. -/
public def threeBlockPreimageProjection
    {H : Type*} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5))) :
    threeBlockPreimage q f →*
      alternatingGroup (Fin 3) × alternatingGroup (Fin (q + 5)) :=
  let i := threeBlockHom q
  let e := MonoidHom.ofInjective (threeBlockHom_injective q)
  e.symm.toMonoidHom.comp
    ((f.comp (threeBlockPreimage q f).subtype).codRestrict
      i.range (fun x => x.2))

public theorem threeBlockPreimageProjection_surjective
    {H : Type*} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5)))
    (hf : Function.Surjective f) :
    Function.Surjective (threeBlockPreimageProjection q f) := by
  intro y
  let i := threeBlockHom q
  let e := MonoidHom.ofInjective (threeBlockHom_injective q)
  obtain ⟨x, hx⟩ := hf (i y)
  have hxE : x ∈ threeBlockPreimage q f := ⟨y, hx.symm⟩
  refine ⟨⟨x, hxE⟩, ?_⟩
  change e.symm ⟨f x, hxE⟩ = y
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  exact hx

public theorem threeBlockHom_projection_apply
    {H : Type*} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5)))
    (x : threeBlockPreimage q f) :
    threeBlockHom q (threeBlockPreimageProjection q f x) = f (x : H) := by
  let i := threeBlockHom q
  let e := MonoidHom.ofInjective (threeBlockHom_injective q)
  change i (e.symm ⟨f (x : H), x.2⟩) = f (x : H)
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f (x : H), x.2⟩)

public theorem threeBlockPreimageProjection_ker_eq_comap
    {H : Type*} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5))) :
    (threeBlockPreimageProjection q f).ker =
      f.ker.comap (threeBlockPreimage q f).subtype := by
  let i := threeBlockHom q
  let e := MonoidHom.ofInjective (threeBlockHom_injective q)
  let r0 := (f.comp (threeBlockPreimage q f).subtype).codRestrict
    i.range (fun x => x.2)
  calc
    (threeBlockPreimageProjection q f).ker = r0.ker :=
      MonoidHom.ker_comp_of_injective r0 e.symm.toMonoidHom e.symm.injective
    _ = f.ker.comap (threeBlockPreimage q f).subtype := by
      ext x
      dsimp [r0]
      constructor
      · intro hx
        have hx0 := MonoidHom.mem_ker.mp hx
        exact MonoidHom.mem_ker.mpr (congrArg Subtype.val hx0)
      · intro hx
        rw [MonoidHom.mem_ker]
        apply Subtype.ext
        exact MonoidHom.mem_ker.mp hx

public theorem threeBlockPreimageProjection_ker_le_center
    {H : Type*} [Group H] (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5)))
    (hker : f.ker ≤ Subgroup.center H) :
    (threeBlockPreimageProjection q f).ker ≤
      Subgroup.center (threeBlockPreimage q f) := by
  rw [threeBlockPreimageProjection_ker_eq_comap]
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hker hx) y.1

set_option backward.isDefEq.respectTransparency false in
/-- A central 3-primary extension splits over the standard
`A_3 × A_(q+5)` block whenever the larger alternating multiplier has no
3-part. -/
public theorem exists_threeBlockPreimage_section_isComplement'
    {H : Type} [Group H] [Finite H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (h3M : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker) :
    ∃ s : alternatingGroup (Fin 3) × alternatingGroup (Fin (q + 5)) →*
        threeBlockPreimage q f,
      (threeBlockPreimageProjection q f).comp s = MonoidHom.id _ ∧
      (threeBlockPreimageProjection q f).ker.IsComplement' s.range := by
  let A := alternatingGroup (Fin 3)
  let B := alternatingGroup (Fin (q + 5))
  let E := threeBlockPreimage q f
  let r := threeBlockPreimageProjection q f
  let jA : A →* A × B := {
    toFun := fun x => (x, 1)
    map_one' := rfl
    map_mul' := fun _ _ => rfl
  }
  let g : A := a3Generator
  let a : alternatingGroup (Fin ((q + 3) + 5)) := threeBlockHom q (g, 1)
  obtain ⟨y, hy, hordy⟩ := exists_threeCycle_lift_order_three
    (q + 3) f hf hker hker3 a (__ch5_ThreeCycleBlockSubextension_threeBlockGenerator_isThreeCycle q)
  obtain ⟨sAH, hsAHg⟩ :=
    exists_cyclic_section_of_order_three g a3_card a3Generator_orderOf y hordy
  have hgenA (x : A) : x ∈ Subgroup.zpowers g := by
    change x ∈ Subgroup.zpowers a3Generator
    rw [a3Generator_zpowers_eq_top]
    trivial
  have hsAH (x : A) : f (sAH x) = threeBlockHom q (x, 1) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgenA x)
    rw [← hk, map_zpow, map_zpow, hsAHg, hy]
    simpa using (map_zpow (threeBlockHom q) (g, 1) k).symm
  let sA : A →* E := sAH.codRestrict E (fun x => ⟨(x, 1), (hsAH x).symm⟩)
  have hsA (x : A) : r (sA x) = (x, 1) := by
    apply threeBlockHom_injective q
    rw [threeBlockHom_projection_apply]
    exact hsAH x
  have hrSurj : Function.Surjective r :=
    threeBlockPreimageProjection_surjective q f hf
  have hrCenter : r.ker ≤ Subgroup.center E :=
    threeBlockPreimageProjection_ker_le_center q f hker
  have hrP : IsPGroup 3 r.ker := by
    rw [threeBlockPreimageProjection_ker_eq_comap]
    exact hker3.comap_subtype
  let ER := prodRightPreimage r
  let DR := prodRightPreimageDerived r
  let rD := prodRightPreimageDerivedProjection r
  have hkerpD : IsPGroup 3 rD.ker := by
    rw [prodRightPreimageDerivedProjection_ker_eq_comap,
      prodRightPreimageProjection_ker_eq_comap]
    exact (hrP.comap_subtype).comap_subtype
  have hdvd : Nat.card rD.ker ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker :=
    by
      dsimp [rD]
      exact alternatingCentralExtensionDerived_ker_card_dvd_multiplier q
        (prodRightPreimageProjection r)
        (prodRightPreimageProjection_surjective r hrSurj)
        (prodRightPreimageProjection_ker_le_center r hrCenter)
  have hright : rD.ker = ⊥ := by
    have hcard : Nat.card rD.ker = 1 := by
      rcases hkerpD.card_eq_or_dvd with h1 | h3
      · exact h1
      · exact False.elim (h3M (h3.trans hdvd))
    exact Subgroup.card_eq_one.mp hcard
  have hrDbij : Function.Bijective rD :=
    ⟨rD.ker_eq_bot_iff.mp hright,
      prodRightPreimageDerivedProjection_surjective r hrSurj⟩
  let eD : DR ≃* B := MulEquiv.ofBijective rD hrDbij
  let sD : B →* E :=
    (ER.subtype.comp DR.subtype).comp eD.symm.toMonoidHom
  have hsD (b : B) : r (sD b) = (1, b) := by
    apply Prod.ext
    · have hmem := (eD.symm b : DR).1.2
      exact Subgroup.mem_bot.mp hmem.1
    · change rD (eD.symm b) = b
      exact eD.apply_symm_apply b
  have hcommKer (b : B) (x : A) : ⁅sD b, sA x⁆ ∈ r.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, hsD, hsA]
    simp [commutatorElement_def]
  have hcommCenter (b : B) (x : A) :
      ⁅sD b, sA x⁆ ∈ Subgroup.center E :=
    hrCenter (hcommKer b x)
  have hcommute (x : A) (b : B) : Commute (sA x) (sD b) := by
    have hOne : ⁅sD b, sA x⁆ = 1 :=
      __ch5_ThreeCycleBlockSubextension_commutatorElement_eq_one_of_left_perfect_of_mem_center
        sD (sA x) (fun z => hcommCenter z x) b
    exact (commutatorElement_eq_one_iff_commute.mp hOne).symm
  let s : A × B →* E := {
    toFun := fun x => sA x.1 * sD x.2
    map_one' := by simp
    map_mul' := by
      intro x z
      simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
      calc
        (sA x.1 * sA z.1) * (sD x.2 * sD z.2) =
            sA x.1 * (sA z.1 * sD x.2) * sD z.2 := by
          simp only [mul_assoc]
        _ = sA x.1 * (sD x.2 * sA z.1) * sD z.2 := by
          rw [(hcommute z.1 x.2).eq]
        _ = _ := by simp only [mul_assoc]
  }
  have hsec : r.comp s = MonoidHom.id (A × B) := by
    apply MonoidHom.ext
    intro x
    change r (sA x.1 * sD x.2) = x
    rw [map_mul, hsA, hsD]
    exact Prod.ext (by simp) (by simp)
  have hdisj : Disjoint r.ker s.range := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    obtain ⟨z, rfl⟩ := hxR
    have hz : z = 1 := by
      have hxz : r (s z) = z := DFunLike.congr_fun hsec z
      have hrone : r (s z) = 1 := MonoidHom.mem_ker.mp hxK
      exact hxz.symm.trans hrone
    rw [hz]
    exact map_one s
  have hmul : (r.ker : Set E) * (s.range : Set E) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    let z := s (r x)
    let k := x * z⁻¹
    have hzr : r z = r x := DFunLike.congr_fun hsec (r x)
    have hk : k ∈ r.ker := by
      rw [MonoidHom.mem_ker]
      dsimp [k]
      rw [map_mul, map_inv, hzr]
      exact mul_inv_cancel _
    have hz : z ∈ s.range := ⟨r x, rfl⟩
    apply Set.mem_mul.mpr
    exact ⟨k, hk, z, hz, by simp [k]⟩
  exact ⟨s, hsec,
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul⟩

/-- A nontrivial central 3-kernel excludes every Sylow 3-subgroup from the
standard `A_3 × A_(q+5)` block preimage once the larger factor multiplier has
no 3-part. -/
public theorem not_sylow_le_threeBlockPreimage_of_not_dvd_multiplier
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (h3ker : 3 ∣ Nat.card f.ker)
    (h3M : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker)
    (P : Sylow 3 H) :
    ¬ (P : Subgroup H) ≤ threeBlockPreimage q f := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hP
  obtain ⟨s, -, hcomp⟩ :=
    exists_threeBlockPreimage_section_isComplement'
      q f hf hker hker3 h3M
  have hkerEq : f.ker = ⊥ :=
    kernel_eq_bot_of_sylow_le_subgroup_of_kernel_comap_isComplement'
      f hker hker3 P (threeBlockPreimage q f) hP s.range (by
        rw [← threeBlockPreimageProjection_ker_eq_comap]
        exact hcomp)
  rw [hkerEq, Subgroup.card_bot] at h3ker
  norm_num at h3ker

/-- The standard three-point block in the degree convention
`((q+3)+5)`, obtained by transporting the first block of
`Fin (3 + (q+5))`. -/
@[expose]
public def threeBlockFirstBlock (q : Nat) :
    Set (Fin ((q + 3) + 5)) :=
  let e : Fin (3 + (q + 5)) ≃ Fin ((q + 3) + 5) := finCongr (by omega)
  e '' finFirstBlock 3 (q + 5)

/-- A Sylow 3-subgroup whose image preserves the standard three-point block
lies in the standard `A_3 × A_(q+5)` block preimage. -/
public theorem sylow_le_threeBlockPreimage_of_mapsTo_threeBlockFirstBlock
    {H : Type*} [Group H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5)))
    (P : Sylow 3 H)
    (hmaps : ∀ x : P, Set.MapsTo
      (f (x : H) : Fin ((q + 3) + 5) → Fin ((q + 3) + 5))
      (threeBlockFirstBlock q) (threeBlockFirstBlock q)) :
    (P : Subgroup H) ≤ threeBlockPreimage q f := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let e : Fin (3 + (q + 5)) ≃ Fin ((q + 3) + 5) := finCongr (by omega)
  let f' : H →* alternatingGroup (Fin (3 + (q + 5))) :=
    e.symm.altCongrHom.toMonoidHom.comp f
  have hP' : (P : Subgroup H) ≤ alternatingBlockPreimage 3 (q + 5) f' := by
    apply sylow_le_alternatingBlockPreimage_of_permBlock
      (p := 3) (by norm_num) 3 (q + 5) f' P
    intro x
    apply perm_mem_permProdBlockHom_range_of_mapsTo_finFirstBlock
    intro y hy
    have hey : e y ∈ threeBlockFirstBlock q := ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzEq⟩ := hmaps x hey
    change e.symm ((f (x : H) : Equiv.Perm _) (e y)) ∈
      finFirstBlock 3 (q + 5)
    rw [← hzEq, e.symm_apply_apply]
    exact hz
  intro x hx
  obtain ⟨z, hz⟩ := hP' hx
  refine ⟨z, ?_⟩
  calc
    threeBlockHom q z = e.altCongrHom
        (alternatingProdBlockHom 3 (q + 5) z) := rfl
    _ = e.altCongrHom (f' x) := congrArg e.altCongrHom hz
    _ = f x := by
      change e.altCongrHom (e.symm.altCongrHom (f x)) = f x
      apply Subtype.ext
      ext y
      simp [Equiv.altCongrHom_apply_coe, Equiv.permCongr_apply]

/-- Standard three-point block exclusion in permutation-action form. -/
public theorem
    not_sylow_image_mapsTo_threeBlockFirstBlock_of_not_dvd_multiplier
    {H : Type} [Group H] [Finite H] [Group.IsPerfect H]
    (q : Nat)
    (f : H →* alternatingGroup (Fin ((q + 3) + 5)))
    (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center H)
    (hker3 : IsPGroup 3 f.ker)
    (h3ker : 3 ∣ Nat.card f.ker)
    (h3M : ¬ 3 ∣ Nat.card
      (alternatingFreeCentralCovering q).toMonoidHom.ker)
    (P : Sylow 3 H) :
    ¬ ∀ x : P, Set.MapsTo
      (f (x : H) : Fin ((q + 3) + 5) → Fin ((q + 3) + 5))
      (threeBlockFirstBlock q) (threeBlockFirstBlock q) := by
  intro hmaps
  exact not_sylow_le_threeBlockPreimage_of_not_dvd_multiplier
    q f hf hker hker3 h3ker h3M P
    (sylow_le_threeBlockPreimage_of_mapsTo_threeBlockFirstBlock
      q f P hmaps)

end GLS3.Chapter5.SchurPresentation
/- END Theory.ThreeCycleBlockSubextension -/

