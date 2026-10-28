module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixEscapingSource

/-!
# The marked even affine group in the actual even branch

When the given ambient Sylow lies in K, the proved normalizer equality gives
N_G(K)=K. The full action marking therefore identifies the affine actor with
the actual even hexacode group. The original U is exactly the translation
subgroup under the same isomorphism, with unchanged point coordinates.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

public theorem original_tripleSix_escaping_even_affine
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t≠1)
    (heven : 2∣(centralizer ({(t:G)} : Set G)).relIndex K)
    (hout : ¬centralizer ({(t:G)} : Set G)≤normalizer (K : Set G))
    (hTK : (T : Subgroup G)≤K) :
    ∃ E : K≃*Multiplicative hexacode ⋊[hexAffineAction.comp hexSign.ker.subtype] HexEvenAutomorphisms,
      (∀ u : U, E (inclusion D.le_component u)=
        SemidirectProduct.inl (tripleSixPointCoordinates D a u)) ∧
      (∀ k : K, (E k).right=a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)) ∧
      (U.subgroupOf K).map E.toMonoidHom=
        (SemidirectProduct.inl : Multiplicative hexacode →*
          Multiplicative hexacode ⋊[hexAffineAction.comp hexSign.ker.subtype] HexEvenAutomorphisms).range := by
  obtain ⟨R,_,_,_,_,E,hU,hmark,_⟩ :=
    original_tripleSix_escaping_affine_model h structural D a t ht heven hout
  let M := normalizer (K : Set G)
  have hMK : M=K := by
    rw [show M=normalizer (K : Set G) from rfl,
      (original_tripleSix_escaping_core h structural D a t ht heven hout).2.2.2.2.2,
      sup_of_le_left hTK]
  have hRe : R≤hexSign.ker := by
    intro r hr
    let x : M := E.symm (SemidirectProduct.inr (⟨r,hr⟩:R))
    let k : K := ⟨x,hMK ▸ x.property⟩
    have hh := hmark k
    change ((E x).right : HexAutomorphisms)=(a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val at hh
    rw [show E x=SemidirectProduct.inr (⟨r,hr⟩:R) from E.apply_symm_apply _] at hh
    change r=(a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val at hh
    rw [hh]
    exact (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).property
  have heR : hexSign.ker≤R := by
    intro r hr
    obtain ⟨q,hq⟩ := a.groupEquiv.surjective (⟨r,hr⟩:HexEvenAutomorphisms)
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) q
    have hh := hmark k
    rw [hq] at hh
    change ((E (inclusion K.le_normalizer k)).right : HexAutomorphisms)=r at hh
    rw [←hh]
    exact (E (inclusion K.le_normalizer k)).right.property
  have hR : R=hexSign.ker := le_antisymm hRe heR
  subst R
  let eKM : K≃*M := MulEquiv.subgroupCongr hMK.symm
  let E' := eKM.trans E
  have hU' (u : U) : E' (inclusion D.le_component u)=
      SemidirectProduct.inl (tripleSixPointCoordinates D a u) := hU u
  refine ⟨E',hU',?_,?_⟩
  · intro k
    exact Subtype.ext (hmark k)
  · apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      exact ⟨tripleSixPointCoordinates D a (⟨u,hu⟩:U),(hU' ⟨u,hu⟩).symm⟩
    · rintro x ⟨v,rfl⟩
      let u := (tripleSixPointCoordinates D a).symm v
      refine ⟨inclusion D.le_component u,u.property,?_⟩
      change E' (inclusion D.le_component u)=SemidirectProduct.inl v
      rw [hU']
      exact congrArg SemidirectProduct.inl ((tripleSixPointCoordinates D a).apply_symm_apply v)

end CFSG.Quasithin.Chapter12.Section07
