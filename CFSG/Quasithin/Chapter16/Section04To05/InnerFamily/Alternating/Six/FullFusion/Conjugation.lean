module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Six.Setup
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport

/-!
# The actual full A₆ conjugation map on the chosen Sylow subgroup

Restrict the transported normalizer action on L to T. Its kernel is
exactly C_T(L). Surjectivity of the normalizer action carries the Sylow
subgroup to an actual Sylow subgroup of Aut(A₆), of order 32. When
C_T(L) = ⟨z⟩ with z an involution, the kernel/image formula gives |T| = 64.
No arbitrary equivalence between automorphism groups is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter16.Intersections.Six.FullFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G} {z : G}

def normalizerConjugation (e : L ≃* alternatingGroup (Fin 6)) :
    normalizer (L : Set G) →* AlternatingSix.ShadowLocal.AutA6 :=
  (MulAut.congr e).toMonoidHom.comp L.normalizerMonoidHom

def sylowConjugation (h : StandardSetup T z L) (e : L ≃* alternatingGroup (Fin 6)) :
    T →* AlternatingSix.ShadowLocal.AutA6 :=
  (normalizerConjugation e).comp (inclusion h.sylow_normalizes)

theorem sylowConjugation_kernel (h : StandardSetup T z L) (e : L ≃* alternatingGroup (Fin 6)) :
    (sylowConjugation h e).ker = (centralizer (L : Set G)).subgroupOf (T : Subgroup G) := by
  ext t
  change (MulAut.congr e) (L.normalizerMonoidHom (inclusion h.sylow_normalizes t)) = 1 ↔ _
  rw [← (MulAut.congr e).map_one, (MulAut.congr e).injective.eq_iff]
  change inclusion h.sylow_normalizes t ∈ L.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

def imageSylow (h : StandardSetup T z L) (e : L ≃* alternatingGroup (Fin 6))
    (hfull : FullAutomorphismCase e) : Sylow 2 AlternatingSix.ShadowLocal.AutA6 :=
  (T.subtype h.sylow_normalizes).mapSurjective hfull

theorem imageSylow_eq_range (h : StandardSetup T z L) (e : L ≃* alternatingGroup (Fin 6))
    (hfull : FullAutomorphismCase e) :
    (imageSylow h e hfull : Subgroup AlternatingSix.ShadowLocal.AutA6) =
      (sylowConjugation h e).range := by
  ext a
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨(n : G), hn⟩, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨inclusion h.sylow_normalizes t, t.property, rfl⟩

theorem sylow_card (h : StandardSetup T z L) (e : L ≃* alternatingGroup (Fin 6))
    (hfull : FullAutomorphismCase e) (hTC : commutingSylow T L = zpowers z) :
    Nat.card T = 64 := by
  let f := sylowConjugation h e
  have hK : Nat.card f.ker = 2 := by
    have he : f.ker.map (T : Subgroup G).subtype = zpowers z := by
      rw [sylowConjugation_kernel, subgroupOf_map_subtype, inf_comm]
      exact hTC
    rw [← card_map_of_injective (T : Subgroup G).subtype_injective, he,
      Nat.card_zpowers, h.involution]
  have hI : Nat.card f.range = 32 := by
    rw [← imageSylow_eq_range h e hfull]
    exact AlternatingSix.ShadowLocal.sylow_card _
  have hh := f.ker.card_mul_index
  rw [index_ker, hK, hI] at hh
  exact hh.symm

end CFSG.Quasithin.Chapter16.Intersections.Six.FullFusion
