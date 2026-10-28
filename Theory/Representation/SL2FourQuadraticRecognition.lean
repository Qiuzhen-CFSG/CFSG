module
public import Theory.Representation.SL2FourProjectiveRecognition.Copies
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors
public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.BinaryOffender.TwoFixedSpaces
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.BinaryOffender.MarkedCentralQuotient
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
/-!
# Recognizing a quadratic Sylow offender for SL₂(4)

A nontrivial binary representation of SL₂(4) which is quadratic on the upper
Sylow four-group and has fixed codimension at most two has the natural module
as its literal quotient by the global fixed space. Central fixed attachments
are retained; neither irreducibility nor a splitting is assumed.

Two opposite Sylow groups generate SL₂(4). Their fixed spaces have zero
intersection in the fixed quotient and codimension at most two. The order-five
minimum degree gives dimension four, so equality makes the fixed planes
complementary. The projective root-pair calculation then constructs natural
coordinates. Perfectness ensures that quotienting the original fixed space
does not create new global fixed vectors.

This is the final module-recognition step of Niles, “Pushing-up in finite
groups” (1979), Lemma 2.8, printed pp.32–33, at q=4, once the action has
descended to SL₂(4) and its offender is Sylow. The upstream odd-kernel and
Sylow-recognition arguments are separate source obligations.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.SL2FourQuadraticRecognition
open SL2FourNatural SL2FourNatural.ProjectiveRecognition
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M]

private theorem upper_opposite_generates :
    BorelFactors.U0 ⊔ BorelFactors.U0.map (MulAut.conj weyl).toMonoidHom = ⊤ := by
  apply top_unique
  intro g _
  apply Matrix.SL2.transvection_induction
    (fun a => a ∈ BorelFactors.U0 ⊔ BorelFactors.U0.map (MulAut.conj weyl).toMonoidHom) ?_
    (fun _ _ => mul_mem) g
  intro i j hij t
  fin_cases i <;> fin_cases j
  · exact False.elim (hij rfl)
  · rw [← BorelFactors.upper_eq_transvection]
    exact mem_sup_left ((BorelFactors.mem_U0 _).mpr ⟨t, rfl⟩)
  · rw [← weyl_upper_weyl]
    apply mem_sup_right
    refine ⟨upper t, (BorelFactors.mem_U0 _).mpr ⟨t, rfl⟩, ?_⟩
    change weyl * upper t * weyl⁻¹ = weyl * upper t * weyl
    rw [weyl_inv]
  · exact False.elim (hij rfl)

omit [FiniteDimensional (ZMod 2) M] in
private theorem faithful_of_nontrivial (σ : Representation (ZMod 2) SL M) (hn : σ ≠ 1) :
    Function.Injective σ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup SL := alternatingFiveEquiv.isSimpleGroup
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · exfalso
    apply hn
    ext g x
    have hg : g ∈ σ.ker := ht ▸ mem_top g
    exact LinearMap.congr_fun hg x

private theorem finrank_ge_four (σ : Representation (ZMod 2) SL M) (hn : σ ≠ 1) :
    4 ≤ Module.finrank (ZMod 2) M := by
  have hc : Nat.card SL = 60 := by
    rw [Nat.card_congr alternatingFiveEquiv.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hh := BinaryPrimeDegree.orderOf_le_finrank σ (faithful_of_nontrivial σ hn)
    (by decide : Nat.Prime 5) (by decide) (by rw [hc]; decide)
  rwa [BinaryPrimeDegree.orderOf_two_mod_five] at hh

omit [FiniteDimensional (ZMod 2) M] in
private theorem fixedSpace_opposite (σ : Representation (ZMod 2) SL M) :
    fixedSpace σ (BorelFactors.U0.map (MulAut.conj weyl).toMonoidHom) =
      (fixedSpace σ BorelFactors.U0).map (σ weyl) := by
  ext x
  constructor
  · intro hx
    refine ⟨σ weyl x, ?_, ?_⟩
    · intro a
      have ha := hx ⟨weyl * a * weyl⁻¹,
        mem_map_of_mem (MulAut.conj weyl).toMonoidHom a.property⟩
      change σ (weyl * a * weyl⁻¹) x = x at ha
      have hh := congrArg (σ weyl) ha
      change σ a.val (σ weyl x) = σ weyl x
      have hw (v : M) : σ weyl (σ weyl v) = v := by
        rw [← Module.End.mul_apply, ← map_mul, weyl_mul_self, map_one]
        rfl
      simpa only [map_mul, Module.End.mul_apply, weyl_inv, hw] using hh
    · rw [← Module.End.mul_apply, ← map_mul, weyl_mul_self, map_one]
      rfl
  · rintro ⟨y, hy, rfl⟩ a
    obtain ⟨b, hb, he⟩ := a.property
    change σ a.val (σ weyl y) = σ weyl y
    rw [← he]
    change σ (weyl * b * weyl⁻¹) (σ weyl y) = σ weyl y
    simp only [map_mul, Module.End.mul_apply, σ.inv_self_apply,
      show σ b y = y from hy ⟨b, hb⟩]

private theorem degree_and_roots (σ : Representation (ZMod 2) SL M)
    (hn : σ ≠ 1) (hfix : fixedSpace σ ⊤ = ⊥)
    (hd : fixedCodim σ BorelFactors.U0 ≤ 2) :
    Module.finrank (ZMod 2) M = 4 ∧
    IsCompl (fixedSpace σ BorelFactors.U0)
      ((fixedSpace σ BorelFactors.U0).map (σ weyl)) := by
  let A := BorelFactors.U0
  let B := A.map (MulAut.conj weyl).toMonoidHom
  have hi : fixedSpace σ A ⊓ fixedSpace σ B = ⊥ := by
    have he : fixedSpace σ (A ⊔ B) = fixedSpace σ A ⊓ fixedSpace σ B :=
      σ.invariants_comp_sup A B
    rw [← he]
    change fixedSpace σ (BorelFactors.U0 ⊔ BorelFactors.U0.map (MulAut.conj weyl).toMonoidHom) = ⊥
    rw [upper_opposite_generates]
    exact hfix
  have hB : fixedCodim σ B = fixedCodim σ A := fixedCodim_map_conj σ A weyl
  have hdim := (fixedSpace σ A).finrank_sup_add_finrank_inf_eq (fixedSpace σ B)
  have hA := fixedCodim_add_finrank σ A
  have hBB := fixedCodim_add_finrank σ B
  have hle := Submodule.finrank_le (fixedSpace σ A ⊔ fixedSpace σ B)
  rw [hi, finrank_bot, add_zero] at hdim
  have hlo := finrank_ge_four σ hn
  have hfour : Module.finrank (ZMod 2) M = 4 := by change fixedCodim σ A ≤ 2 at hd; omega
  have hs : fixedSpace σ A ⊔ fixedSpace σ B = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change fixedCodim σ A ≤ 2 at hd
    omega
  refine ⟨hfour, ?_⟩
  rw [← fixedSpace_opposite σ]
  exact ⟨disjoint_iff.mpr hi, codisjoint_iff.mpr hs⟩

/-- A quadratic upper Sylow offender with no global fixed vectors is the literal natural module. -/
theorem natural_of_fixed_free (σ : Representation (ZMod 2) SL M)
    (hn : σ ≠ 1) (hfix : fixedSpace σ ⊤ = ⊥)
    (hq : IsQuadratic σ BorelFactors.U0)
    (hd : fixedCodim σ BorelFactors.U0 ≤ 2) :
    ∃ e : M ≃ₗ[ZMod 2] SL2FourNatural.V,
      ∀ g v, e (σ g v) = specialLinearNatural 2 g (e v) := by
  obtain ⟨hdim, hcompl⟩ := degree_and_roots σ hn hfix hd
  let A := fixedSpace σ BorelFactors.U0
  have hu (t : F) : upper t ∈ BorelFactors.U0 :=
    (BorelFactors.mem_U0 _).mpr ⟨t, rfl⟩
  have hp : RootPair σ weyl A := ⟨hcompl,
    fun t x hx => hx ⟨upper t, hu t⟩,
    fun t x a => hq a a.property (upper t) (hu t) x⟩
  have hdiag : ∀ x ∈ A, σ diagonalWord x ∈ A := by
    intro x hx a
    obtain ⟨t, ht⟩ := (BorelFactors.mem_U0 a.val).mp a.property
    have he : ∀ t : F, upper t * diagonalWord = diagonalWord * upper (ProjectiveRecognition.omega * t) := by
      decide +kernel
    change σ a.val (σ diagonalWord x) = σ diagonalWord x
    rw [← ht, ← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply]
    have hh : σ (upper (ProjectiveRecognition.omega * t)) x = x :=
      hx ⟨_, hu (ProjectiveRecognition.omega * t)⟩
    rw [hh]
  let : Finite M := Module.finite_of_finite (ZMod 2)
  obtain ⟨s, e, he⟩ := natural_coordinates hp hdiag
  have hs : s = 1 := by
    have hh := e.finrank_eq
    rw [hdim, Module.finrank_pi_fintype, finrank_vector] at hh
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hh
    omega
  subst s
  refine ⟨e.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) SL2FourNatural.V), ?_⟩
  intro g v
  exact he g v 0

private theorem slPerfect : Group.IsPerfect SL := by
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := alternatingFiveEquiv.symm.toMonoidHom)
    alternatingFiveEquiv.symm.surjective

omit [FiniteDimensional (ZMod 2) M] in
private theorem fixed_quotient_fixed_free (σ : Representation (ZMod 2) SL M) :
    fixedSpace (fixedQuotient σ ⊤) ⊤ = ⊥ := by
  let : Group.IsPerfect SL := slPerfect
  have hp : IsPPerfect 2 (⊤ : Subgroup SL) := by
    intro N hN hQ
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial ((⊤ : Subgroup SL) ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent ((⊤ : Subgroup SL) ⧸ N) := hQ.isNilpotent
    exact Group.IsPerfect.not_isSolvable ((⊤ : Subgroup SL) ⧸ N) inferInstance
  apply le_bot_iff.mp
  intro q hq
  obtain ⟨v, rfl⟩ := (fixedSpace σ ⊤).mkQ_surjective q
  have hv := fixed_of_pPerfect_central_kernel σ ⊤ hp (fixedSpace σ ⊤).mkQ
    (by rw [Submodule.ker_mkQ]) v (fun a => hq a)
  exact (Submodule.Quotient.mk_eq_zero _).mpr hv

/-- The literal fixed quotient of an arbitrary nontrivial quadratic Sylow-offender
module is natural. No irreducibility, splitting, or root-space data is assumed. -/
theorem natural_fixed_quotient (σ : Representation (ZMod 2) SL M)
    (hn : σ ≠ 1) (hq : IsQuadratic σ BorelFactors.U0)
    (hd : fixedCodim σ BorelFactors.U0 ≤ 2) :
    ∃ e : (M ⧸ fixedSpace σ ⊤) ≃ₗ[ZMod 2] SL2FourNatural.V,
      ∀ g v, e (fixedQuotient σ ⊤ g v) = specialLinearNatural 2 g (e v) := by
  let : Group.IsPerfect SL := slPerfect
  let W := fixedSubrepresentation σ ⊤
  have hnon : ¬ (⊤ : Subgroup SL) ≤ σ.ker := by
    intro h
    apply hn
    ext g x
    exact LinearMap.congr_fun (h (mem_top g)) x
  have hnonQ : fixedQuotient σ ⊤ ≠ 1 := by
    intro he
    exact fixedQuotient_noncentral σ ⊤ hnon (by rw [he]; intro g hg; rfl)
  have hqQ : IsQuadratic (fixedQuotient σ ⊤) BorelFactors.U0 :=
    quadratic_of_equivariant_surjection σ W.quotientRepresentation
      W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective
      (fun g v => (W.quotientRepresentation_mk g v).symm) BorelFactors.U0 hq
  have hdQ : fixedCodim (fixedQuotient σ ⊤) BorelFactors.U0 ≤ 2 :=
    (fixedCodim_le_of_equivariant_surjection σ W.quotientRepresentation
      W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective
      (fun g v => (W.quotientRepresentation_mk g v).symm) BorelFactors.U0).trans hd
  exact natural_of_fixed_free _ hnonQ (fixed_quotient_fixed_free σ) hqQ hdQ

end Representation.SL2FourQuadraticRecognition
