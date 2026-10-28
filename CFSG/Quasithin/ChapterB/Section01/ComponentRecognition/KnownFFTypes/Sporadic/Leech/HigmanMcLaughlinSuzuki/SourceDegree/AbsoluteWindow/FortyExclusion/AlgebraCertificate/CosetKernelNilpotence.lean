module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.AlgebraCertificate.CosetModule
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.OrbitQuotient
public import Mathlib.RingTheory.Artinian.Ring

/-!
# Nilpotence of the universal HS fixed-vector kernel

Write R for the literal binary HS algebra, I for the five-center norm ideal,
and P for the published two-subgroup. The universal module is R/L with the
left ideal L = I + span {p - 1 | p ∈ P} from `CosetModule`.

Every maximal left quotient R/M with I ≤ M has a nonzero P-fixed vector:
P is a two-group and R/M is a finite binary vector space. Sending a to a • v
therefore factors through R/L and surjects onto the simple module R/M. Hence
the kernel of the universal action lies in the Jacobson radical of I.
The ring R/I is finite, so its Jacobson radical is nilpotent. Pulling this
nilpotence back gives the required uniform bound on products in the kernel.
The quotient by L is used only as a left module; only I is quotiented as a ring.

`of_cosetNorm_small_action` applies this result to the published constructor,
leaving precisely the independent small-action calculation as explicit data.
Final construction of the source norm certificate remains with its assembly.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS paragraph, author-preprint p.16; Aschbacher--Smith K.4,
printed p.457. This proves the universal algebra prerequisite for the source
exclusion, without assuming that HS is simple or that P is Sylow.
-/

public section
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate

private noncomputable instance binaryAlgebraFinite : Finite BinaryAlgebra := by
  let : Finite KnownSimple.SporadicName.hs.Carrier :=
    inferInstanceAs (Finite _root_.Sporadic.LeechRelated.HS.Carrier)
  exact Finite.of_injective
    (fun x : BinaryAlgebra => (x.coeff : KnownSimple.SporadicName.hs.Carrier → ZMod 2))
    (DFunLike.coe_injective.comp MonoidAlgebra.coeff_injective)

set_option backward.isDefEq.respectTransparency false in
/-- Every simple left quotient by an ideal containing the norm ideal is a
quotient of the literal universal left module. The fixed-vector and norm relations are both
checked on the chosen generating vector. -/
theorem cosetNorm_surjects_simple_quotient (M : Ideal BinaryAlgebra) [M.IsMaximal]
    (hI : fiveNormIdeal.asIdeal ≤ M) :
    ∃ f : (BinaryAlgebra ⧸ cosetNormRelations) →ₗ[BinaryAlgebra] (BinaryAlgebra ⧸ M),
      Function.Surjective f := by
  let : IsSimpleModule BinaryAlgebra (BinaryAlgebra ⧸ M) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.IsMaximal.out (I := M))
  let : Nontrivial (BinaryAlgebra ⧸ M) := IsSimpleModule.nontrivial BinaryAlgebra _
  let : Finite (BinaryAlgebra ⧸ M) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective M)
  let e := RestrictScalars.addEquiv (ZMod 2) BinaryAlgebra (BinaryAlgebra ⧸ M)
  let : Finite (RestrictScalars (ZMod 2) BinaryAlgebra (BinaryAlgebra ⧸ M)) :=
    Finite.of_equiv _ e.symm.toEquiv
  let : Nontrivial (RestrictScalars (ZMod 2) BinaryAlgebra (BinaryAlgebra ⧸ M)) :=
    e.toEquiv.nontrivial
  let ρ := Representation.ofModule (k := ZMod 2)
    (G := KnownSimple.SporadicName.hs.Carrier) (BinaryAlgebra ⧸ M)
  obtain ⟨v, hv, hfix⟩ :=
    BinaryLinearThree.IrreducibleCatalogue.binary_pGroup_fixed_vector
      (ρ.comp twoSubgroup.subtype) twoSubgroup_isPGroup
  let w := e v
  have hw : w ≠ 0 := by
    intro h
    apply hv
    exact e.injective (h.trans e.map_zero.symm)
  have hfixed (p : twoSubgroup) : MonoidAlgebra.single p.val (1 : ZMod 2) • w = w := by
    have h := hfix p
    change ρ p.val v = v at h
    have hh : ρ.asAlgebraHom (MonoidAlgebra.single p.val 1) v = v := by
      simpa only [Representation.asAlgebraHom_single, one_smul] using h
    rw [Representation.ofModule_asAlgebraHom_apply_apply] at hh
    exact congrArg e hh
  have hIann (a : BinaryAlgebra) (ha : a ∈ fiveNormIdeal.asIdeal)
      (q : BinaryAlgebra ⧸ M) : a • q = 0 := by
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective M q
    change (Submodule.Quotient.mk (a * b) : BinaryAlgebra ⧸ M) = 0
    exact (Submodule.Quotient.mk_eq_zero M).mpr
      (hI (fiveNormIdeal.mul_mem_right a b ha))
  let f := LinearMap.toSpanSingleton BinaryAlgebra (BinaryAlgebra ⧸ M) w
  have hL : cosetNormRelations ≤ LinearMap.ker f := by
    apply sup_le
    · intro a ha
      exact hIann a ha w
    · apply Ideal.span_le.mpr
      rintro a ⟨p, rfl⟩
      change (MonoidAlgebra.single p.val (1 : ZMod 2) - 1) • w = 0
      rw [sub_smul, one_smul, hfixed, sub_self]
  have hf : Function.Surjective f := IsSimpleModule.toSpanSingleton_surjective BinaryAlgebra hw
  refine ⟨cosetNormRelations.liftQ f hL, ?_⟩
  intro q
  obtain ⟨a, ha⟩ := hf q
  exact ⟨cosetNormRelations.mkQ a, ha⟩

/-- Vanishing on the universal action implies membership in every maximal
left ideal containing the norm ideal. -/
theorem cosetKernel_le_jacobson :
    (TwoSidedIdeal.ker cosetNormRepresentation.asAlgebraHom).asIdeal ≤
      fiveNormIdeal.asIdeal.jacobson := by
  intro x hx
  rw [Ideal.jacobson, Ideal.mem_sInf]
  intro M hM
  let : M.IsMaximal := hM.2
  obtain ⟨f, hf⟩ := cosetNorm_surjects_simple_quotient M hM.1
  have hx0 := (TwoSidedIdeal.mem_ker _).mp hx
  have hkill (u : BinaryAlgebra ⧸ cosetNormRelations) : x • u = 0 := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective cosetNormRelations u
    have h := LinearMap.congr_fun hx0 (cosetNormVector y)
    rw [cosetNorm_action_vector, LinearMap.zero_apply] at h
    exact h
  obtain ⟨u, hu⟩ := hf (M.mkQ 1)
  have hh : x • M.mkQ 1 = 0 := by
    rw [← hu, ← f.map_smul, hkill, map_zero]
  have hh' : M.mkQ x = 0 := by
    simpa only [← map_smul, smul_eq_mul, mul_one] using hh
  exact (Submodule.Quotient.mk_eq_zero M).mp hh'

/-- Products of a uniform number of elements of the universal action kernel
belong to the literal five-center norm ideal. -/
theorem cosetKernel_nilpotent :
    ∃ r : ℕ, ∀ xs : List BinaryAlgebra, xs.length = r →
      (∀ x ∈ xs, cosetNormRepresentation.asAlgebraHom x = 0) →
        xs.prod ∈ fiveNormIdeal := by
  let I := fiveNormIdeal.asIdeal
  let A := BinaryAlgebra ⧸ I
  let q : BinaryAlgebra →+* A := Ideal.Quotient.mk I
  let : Finite A := Finite.of_surjective q Ideal.Quotient.mk_surjective
  obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have hrad (x : BinaryAlgebra) (hx : cosetNormRepresentation.asAlgebraHom x = 0) :
      q x ∈ Ideal.jacobson (⊥ : Ideal A) := by
    have h := cosetKernel_le_jacobson ((TwoSidedIdeal.mem_ker _).mpr hx)
    have he : Ideal.comap q (Ideal.jacobson (⊥ : Ideal A)) = I.jacobson := by
      rw [Ideal.comap_jacobson_of_surjective Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    change x ∈ Ideal.comap q (Ideal.jacobson (⊥ : Ideal A))
    rw [he]
    exact h
  have hprod (xs : List BinaryAlgebra)
      (hx : ∀ x ∈ xs, cosetNormRepresentation.asAlgebraHom x = 0) :
      q xs.prod ∈ (Ideal.jacobson (⊥ : Ideal A)) ^ xs.length := by
    induction xs with
    | nil =>
      simp only [List.prod_nil, List.length_nil, map_one, Submodule.pow_zero,
        Ideal.one_eq_top, Submodule.mem_top]
    | cons x xs ih =>
      rw [List.prod_cons, map_mul, List.length_cons, Ideal.IsTwoSided.pow_succ]
      exact Ideal.mul_mem_mul (hrad x (hx x (by simp)))
        (ih (fun y hy => hx y (by simp [hy])))
  refine ⟨r, fun xs hlen hx => ?_⟩
  have h := hprod xs hx
  rw [hlen, hr] at h
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (Ideal.mem_bot.mp h)

/-- Discharge the universal-kernel premise of `of_cosetNorm_action`.
The dimension bound and nilpotence relative to the universal action are the
independent finite calculation; no further universal-kernel premise remains. -/
noncomputable def of_cosetNorm_small_action
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) KnownSimple.SporadicName.hs.Carrier V)
    (hd : Module.finrank (ZMod 2) V * Module.finrank (ZMod 2) V < 1600)
    (s : ℕ)
    (hs : ∀ xs : List BinaryAlgebra, xs.length = s →
      (∀ x ∈ xs, ρ.asAlgebraHom x = 0) →
        cosetNormRepresentation.asAlgebraHom xs.prod = 0) : NormCertificate :=
  of_cosetNorm_action ρ hd (Classical.choose cosetKernel_nilpotent) s
    (Classical.choose_spec cosetKernel_nilpotent) hs

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion.AlgebraCertificate
