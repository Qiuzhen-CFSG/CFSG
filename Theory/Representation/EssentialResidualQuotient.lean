module
public import Theory.Representation.SubspaceQuotient
public import Theory.Representation.SubrepresentationLattice
public import Theory.Representation.BinaryOffender.MovedSpaceTransport
public import Theory.Representation.BinaryOffender.CentralSectionAction
public import Theory.Representation.BinaryOffender.PPerfectFixedLift
public import Theory.Representation.BinarySylowFixedSpace
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Essential simple quotients detected by the two-residual

Choose an invariant subspace maximal among those not containing the residual
commutator space. Its literal quotient contains the image of that space as a
simple submodule contained in every nonzero submodule. Two-perfectness rules
out fixed vectors: a central residual-moved space would give a homomorphism
into an elementary abelian two-group. Odd Sylow-coset averaging then places
every Sylow-fixed vector inside the simple image.

The averaging lemma only assumes that the chosen vector has fixed image;
it does not require the entire quotient action to be trivial. All quotient
maps and representations are the original linear maps.

Source application: Aschbacher–Smith, original 3.1.9(5), printed p.578.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.EssentialResidualQuotient
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The invariant commutator submodule for a normal actor. -/
def moved (K : Subgroup G) [K.Normal] : Subrepresentation ρ where
  toSubmodule := subspaceCommutator ρ ⊤ K
  apply_mem_toSubmodule g v hv :=
    (subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (show (⊤ : Subgroup G) ≤ normalizer (K : Set G) from le_normalizer_of_normal)
      (mem_top g) v).2 hv

/-- Nontrivial residual action gives a nonzero literal moved submodule. -/
theorem moved_ne_bot_of_not_le_ker (K : Subgroup G) [K.Normal]
    (hn : ¬ K ≤ ρ.ker) : moved ρ K ≠ ⊥ := by
  intro hz
  have hz' : subspaceCommutator ρ ⊤ K = ⊥ := congrArg Subrepresentation.toSubmodule hz
  have hf := (subspaceCommutator_eq_bot_iff ρ ⊤ K).mp hz'
  apply hn
  intro k hk
  apply LinearMap.ext
  intro v
  exact hf Submodule.mem_top ⟨k,hk⟩

private theorem essential_image_of_maximal
    (D W : Subrepresentation ρ) (hW : ¬ D ≤ W)
    (hmax : ∀ N : Subrepresentation ρ, W < N → D ≤ N) :
    W.quotientImage D ≠ ⊥ ∧
      ∀ N : Subrepresentation W.quotientRepresentation, N ≠ ⊥ → W.quotientImage D ≤ N := by
  refine ⟨fun he => hW ((W.quotientImage_eq_bot_iff D).mp he), ?_⟩
  intro N hN
  let P : Subrepresentation ρ := {
    toSubmodule := N.toSubmodule.comap W.toSubmodule.mkQ
    apply_mem_toSubmodule g v hv := N.apply_mem_toSubmodule g hv }
  have hWP : W ≤ P := by
    intro v hv
    change W.toSubmodule.mkQ v ∈ N
    have hz : W.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hv
    rw [hz]
    exact N.toSubmodule.zero_mem
  have hlt : W < P := lt_of_le_of_ne hWP (by
    intro he
    apply hN
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro q hq
    obtain ⟨v,rfl⟩ := W.toSubmodule.mkQ_surjective q
    have hv : v ∈ P := hq
    rw [←he] at hv
    exact (Submodule.Quotient.mk_eq_zero _).mpr hv)
  rintro q ⟨v,hv,rfl⟩
  exact hmax P hlt hv

/-- A quotient chosen maximally to retain a prescribed submodule has an
essential simple image of that submodule. -/
theorem exists_essential_quotient [FiniteDimensional (ZMod 2) V]
    (D : Subrepresentation ρ) (hD : D ≠ ⊥) :
    ∃ W : Subrepresentation ρ,
      ¬ D ≤ W ∧ (∀ N : Subrepresentation ρ, W < N → D ≤ N) ∧
      IsIrreducible (W.quotientImage D).toRepresentation ∧
      ∀ N : Subrepresentation W.quotientRepresentation, N ≠ ⊥ → W.quotientImage D ≤ N := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Subrepresentation ρ) :=
    Finite.of_injective (fun N : Subrepresentation ρ => (N : Set V)) SetLike.coe_injective
  obtain ⟨W,hW,hmax⟩ := Set.Finite.exists_maximal
    (Set.toFinite {N : Subrepresentation ρ | ¬ D ≤ N})
    (show Set.Nonempty {N : Subrepresentation ρ | ¬ D ≤ N} from
      ⟨⊥, fun hh => hD (le_antisymm hh bot_le)⟩)
  have hmax' : ∀ N : Subrepresentation ρ, W < N → D ≤ N := by
    intro N hN
    by_contra hh
    exact (not_le_of_gt hN) (hmax hh hN.le)
  obtain ⟨hn,he⟩ := essential_image_of_maximal ρ D W hW hmax'
  refine ⟨W,hW,hmax',(Subrepresentation.irreducible_iff_isAtom _).mpr ⟨hn,?_⟩,he⟩
  intro N hN
  by_contra hNb
  exact (not_le_of_gt hN) (he N hNb)

private theorem moved_image_displacement (K : Subgroup G) [K.Normal]
    (W : Subrepresentation ρ) (k : K) (q : V ⧸ W.toSubmodule) :
    W.quotientRepresentation k q - q ∈ W.quotientImage (moved ρ K) := by
  obtain ⟨v,rfl⟩ := W.toSubmodule.mkQ_surjective q
  exact ⟨ρ k v - v,Submodule.subset_span ⟨k,k.property,v,Submodule.mem_top,rfl⟩,
    map_sub _ _ _⟩

private theorem moved_image_not_fixed (K : Subgroup G) [K.Normal]
    (hK : IsPPerfect 2 K) (W : Subrepresentation ρ) (hW : ¬ moved ρ K ≤ W) :
    ¬ (W.quotientImage (moved ρ K)).toSubmodule ≤ fixedSpace W.quotientRepresentation K := by
  intro hh
  have hfixed (q : V ⧸ W.toSubmodule) : q ∈ fixedSpace W.quotientRepresentation K := by
    apply fixed_of_pPerfect_central_kernel W.quotientRepresentation K hK
      (W.quotientImage (moved ρ K)).toSubmodule.mkQ
    · simpa only [Submodule.ker_mkQ] using hh
    · intro k
      exact (Submodule.Quotient.eq _).mpr (moved_image_displacement ρ K W k q)
  apply hW
  apply Submodule.span_le.mpr
  rintro _ ⟨k,hk,v,_,rfl⟩
  exact (Submodule.Quotient.eq W.toSubmodule).mp (hfixed (W.toSubmodule.mkQ v) ⟨k,hk⟩)

private theorem fixed_eq_bot_of_essential_moved (K : Subgroup G) [K.Normal]
    (hK : IsPPerfect 2 K) (W : Subrepresentation ρ) (hW : ¬ moved ρ K ≤ W)
    (hess : ∀ N : Subrepresentation W.quotientRepresentation,
      N ≠ ⊥ → W.quotientImage (moved ρ K) ≤ N) :
    fixedSpace W.quotientRepresentation K = ⊥ := by
  let C : Subrepresentation W.quotientRepresentation := {
    toSubmodule := fixedSpace W.quotientRepresentation K
    apply_mem_toSubmodule g v hv :=
      (fixedSpace_stable_of_normalizes W.quotientRepresentation
        (show (⊤ : Subgroup G) ≤ normalizer (K : Set G) from le_normalizer_of_normal)
        (mem_top g) v).2 hv }
  by_contra hn
  have hC : C ≠ ⊥ := fun he => hn (congrArg Subrepresentation.toSubmodule he)
  exact moved_image_not_fixed ρ K hK W hW (hess C hC)

/-- Odd-coset averaging only needs triviality of the image of the chosen vector. -/
theorem fixed_lift_of_displacement [Finite G] (S : Sylow 2 G)
    (U : Submodule (ZMod 2) V) (v : V) (hv : v ∈ fixedSpace ρ S)
    (hU : ∀ g, ρ g v - v ∈ U) :
    ∃ w : V, (∀ g, ρ g w = w) ∧ v - w ∈ U := by
  classical
  let _ := Fintype.ofFinite (G ⧸ (S : Subgroup G))
  let f : G ⧸ (S : Subgroup G) → V := Quotient.lift (fun g => ρ g v) (by
    intro a b hab
    have hs : a⁻¹ * b ∈ S := QuotientGroup.leftRel_apply.mp hab
    have hf : ρ (a⁻¹ * b) v = v := hv ⟨_,hs⟩
    calc
      ρ a v = ρ a (ρ (a⁻¹ * b) v) := congrArg (ρ a) hf.symm
      _ = ρ b v := by simp [← Module.End.mul_apply,← map_mul])
  have hf (g : G) (q : G ⧸ (S : Subgroup G)) : ρ g (f q) = f (g • q) := by
    induction q using Quotient.inductionOn with
    | h a => exact (congrArg (fun t : Module.End (ZMod 2) V => t v) (ρ.map_mul g a)).symm
  let w : V := ∑ q, f q
  refine ⟨w,?_,?_⟩
  · intro g
    simp only [w,map_sum,hf]
    exact Equiv.sum_comp (MulAction.toPerm g) f
  · have hq (q : G ⧸ (S : Subgroup G)) : U.mkQ (f q) = U.mkQ v := by
      induction q using Quotient.inductionOn with
      | h a => exact (Submodule.Quotient.eq U).mpr (hU a)
    have hn : (Fintype.card (G ⧸ (S : Subgroup G)) : ZMod 2) = 1 := by
      have ho := S.not_dvd_index
      rw [Subgroup.index,Nat.card_eq_fintype_card] at ho
      have hm : Fintype.card (G ⧸ (S : Subgroup G)) % 2 = 1 := by omega
      exact (ZMod.natCast_eq_natCast_iff' _ 1 2).mpr hm
    have hw : U.mkQ w = U.mkQ v := by
      simp only [w,map_sum,hq,Finset.sum_const,Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul (ZMod 2),hn,one_smul]
    exact (Submodule.Quotient.eq U).mp hw.symm

/-- In a quotient with no residual-fixed vectors, Sylow-fixed vectors lie in the
literal residual-moved image. -/
theorem sylow_fixed_le_image [Finite G] (K : Subgroup G) [K.Normal]
    (W : Subrepresentation ρ) (S : Sylow 2 G) (hKS : K ⊔ (S : Subgroup G) = ⊤)
    (hfixed : fixedSpace W.quotientRepresentation K = ⊥) :
    fixedSpace W.quotientRepresentation S ≤ (W.quotientImage (moved ρ K)).toSubmodule := by
  intro v hv
  obtain ⟨w,hw,hvw⟩ := fixed_lift_of_displacement W.quotientRepresentation S
    (W.quotientImage (moved ρ K)).toSubmodule v hv (by
      intro g
      obtain ⟨k,hk,s,hs,rfl⟩ := mem_sup_of_normal_left.mp (hKS.ge (mem_top g))
      have hsf : W.quotientRepresentation s v = v := hv ⟨s,hs⟩
      rw [map_mul,Module.End.mul_apply,hsf]
      exact moved_image_displacement ρ K W ⟨k,hk⟩ v)
  have hw0 : w = 0 := by
    have hm : w ∈ fixedSpace W.quotientRepresentation K := fun k => hw k
    rwa [hfixed,Submodule.mem_bot] at hm
  simpa only [hw0,sub_zero] using hvw

/-- A maximal quotient retaining residual movement has a noncentral essential
simple socle, no residual-fixed vectors, and all Sylow-fixed vectors in that socle. -/
theorem exists_residual_quotient [Finite G] [FiniteDimensional (ZMod 2) V]
    (hn : moved ρ (pResidual 2 G) ≠ ⊥) :
    ∃ W : Subrepresentation ρ,
      ¬ moved ρ (pResidual 2 G) ≤ W ∧
      (∀ N : Subrepresentation ρ, W < N → moved ρ (pResidual 2 G) ≤ N) ∧
      IsIrreducible (W.quotientImage (moved ρ (pResidual 2 G))).toRepresentation ∧
      (∀ N : Subrepresentation W.quotientRepresentation, N ≠ ⊥ →
        W.quotientImage (moved ρ (pResidual 2 G)) ≤ N) ∧
      fixedSpace W.quotientRepresentation (pResidual 2 G) = ⊥ ∧
      (∀ S : Sylow 2 G, fixedSpace W.quotientRepresentation S ≤
        (W.quotientImage (moved ρ (pResidual 2 G))).toSubmodule) := by
  obtain ⟨W,hW,hmax,hi,he⟩ := exists_essential_quotient ρ _ hn
  have hf := fixed_eq_bot_of_essential_moved ρ _ (isPPerfect_pResidual 2) W hW he
  exact ⟨W,hW,hmax,hi,he,hf,fun S => sylow_fixed_le_image ρ _ W S
    (pResidual_sup_sylow_eq_top S) hf⟩

/-- Every nonzero Sylow-stable seed has a nonzero Sylow-fixed vector. -/
theorem exists_nonzero_fixed_seed [Finite G] [FiniteDimensional (ZMod 2) V]
    (S : Sylow 2 G) (X : Submodule (ZMod 2) V)
    (hX : (S : Subgroup G) ≤ subspaceStabilizer ρ X) (hne : X ≠ ⊥) :
    ∃ v : V, v ∈ X ∧ v ≠ 0 ∧ v ∈ fixedSpace ρ S := by
  let : Nontrivial X := Submodule.nontrivial_iff_ne_bot.mpr hne
  let σ := Representation.subrepresentation (ρ.comp (S : Subgroup G).subtype) X
    (fun s v hv => (hX s.property v).2 hv)
  have hc : ringChar (ZMod 2) = 2 := ringChar.eq (ZMod 2) 2
  obtain ⟨v,hv,hfix⟩ := pGroup_fix_nonzero_vector
    (by rw [hc]; decide) (by rw [hc]; exact S.isPGroup') σ
  exact ⟨v,v.property,fun hz => hv (Subtype.ext hz),
    fun s => congrArg Subtype.val (hfix s)⟩

end Representation.EssentialResidualQuotient
