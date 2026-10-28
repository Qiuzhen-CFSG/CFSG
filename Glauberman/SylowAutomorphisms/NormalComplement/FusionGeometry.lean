module

public import Glauberman.SylowAutomorphisms.NormalComplement.Contracts
public import Glauberman.SylowAutomorphisms.NormalComplement.ComplementObstruction
public import Glauberman.SylowAutomorphisms.NormalComplement.FusionGeometry.Sylow

/-!
# Excluding odd displacement in a Sylow pointwise fixer

A nonzero elementary abelian displacement subgroup U and its odd actor x
would yield a contradiction. Restrict the actors to B = ⟨U,x⟩ and use
the faithful extension H = G ⋊ U. Z-star and the center-containing fusion
selection produce Q and an odd mover h in G. Transport them into K = G ⋊ B.

The actual local group J = N_K(Q) ∩ N_K(C_T(Q)) normalizes
V = Ω₁(Z(C_T(Q))) and W = V ∩ G = V ∩ S, with V = U × W.
The odd index of H and the witness's normalizer-Sylow field construct a
Sylow subgroup of J with image J ∩ T. It centralizes U. Moreover x belongs
to J and centralizes W. The previously proved complement obstruction
therefore forces h to fix U, contradicting the selected fusion of t ∈ U.

The only source input left explicit is the elementary central-involution
fusion theorem supplied in the task. This exclusion is independent of the
construction of odd displacement and of the abelian-Sylow theorem.

Source: Glauberman, Math. Z. 93 (1966), Theorem 1(b), p.158,
DOI 10.1007/BF01111033. The parent NormalComplement module owns the
subsequent normal-complement assembly with the independent OddActor input.
-/

public section
namespace Glauberman.SylowAutomorphisms.NormalComplement
open Subgroup SemidirectProduct FusionGeometry
universe u

/-- The source fusion geometry excludes odd displacement in any faithful
finite action fixing a Sylow two-subgroup pointwise. -/
theorem faithful_fixing_action_no_oddDisplacement
    (fusion : SylowCentralFusion.CentralInvolutionFusion.{u})
    {G A : Type u} [Group G] [Group A] [Finite G] [Finite A]
    (φ : A →* MulAut G) (hf : Function.Injective φ)
    (hcore : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (hfix : ∀ a : A, ∀ s ∈ (S : Subgroup G), φ a s = s)
    (d : OddDisplacement A) : False := by
  let _ : Finite (Extension φ d) := Finite.of_equiv (G × actors d) equivProd.symm
  obtain ⟨t, _, w, hZ, _⟩ := exists_center_fusion fusion φ hf hcore d S hfix
  obtain ⟨T, hT, P, hP⟩ := exists_compatible_sylows φ d S hfix t w
  let _ : IsElementaryAbelian 2 (omegaCenter φ d S hfix w.subgroup) :=
    Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  apply mover_moves φ d S hfix t w
  apply actor_fixed_of_complement_geometry (extensionAction φ d) (restrictedDisplacement d)
    (localNormalizer φ d S hfix w.subgroup)
    (omegaCenter φ d S hfix w.subgroup) (basePart φ d S hfix w.subgroup)
    (localNormalizer_normalizes_omegaCenter φ d S hfix w.subgroup)
    (localNormalizer_normalizes_basePart φ d S hfix w.subgroup)
    (actorImage_le_omegaCenter φ d S hfix w.subgroup w.le_sylow)
    (basePart_isCompl_actorImage φ d S hfix w.subgroup w.le_sylow) P
    _ (actor_mem_localNormalizer φ d S hfix w.subgroup w.le_sylow hZ _)
    (actor_centralizes_basePart φ d S hfix w.subgroup _)
    _ (mover_mem_localNormalizer φ d S hfix t w) (mover_mem_base φ d S hfix t w)
    (⟨t, mem_sup_left t.property⟩ : actors d) t.property
  intro a ha
  apply Subgroup.centralizer_le_normalizer
  apply mem_centralizer_iff.mpr
  rintro _ ⟨b, hb, rfl⟩
  have haT : (a : Extension φ d) ∈ sylowImage φ d S hfix := by
    have hh : (a : Extension φ d) ∈ (P : Subgroup _).map
        (localNormalizer φ d S hfix w.subgroup).subtype := ⟨a, ha, rfl⟩
    rw [hP, hT] at hh
    exact hh.1
  exact (sylowImage_commutes_actor φ d S hfix b hb a haT).symm

/-- The exclusion needed in Glauberman Theorem 1(b), for the literal
pointwise automorphism fixer. No abelian-Sylow, solvability or Schreier
hypothesis is used. -/
theorem fixingSubgroup_no_oddDisplacement
    (fusion : SylowCentralFusion.CentralInvolutionFusion.{u})
    {G : Type u} [Group G] [Finite G]
    (hcore : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (d : OddDisplacement (fixingSubgroup (MulAut G) (S : Set G))) : False := by
  apply faithful_fixing_action_no_oddDisplacement fusion
    (fixingSubgroup (MulAut G) (S : Set G)).subtype Subtype.val_injective hcore S _ d
  intro a s hs
  exact (mem_fixingSubgroup_iff (MulAut G)).mp a.property s hs

end Glauberman.SylowAutomorphisms.NormalComplement
