module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.CentralizerReduction
public import CFSG.Quasithin.Defs

/-!
# The earlier-source A₆ centralizer equality

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.22(2), printed p.567.

Work inside J = C_G(t). The inputs are K normal in J, K ≅ A₆, S Sylow in J,
H = KS, J = KS C_J(K), characteristic two of C_J(K), and the surjective
actual conjugation action on K. The crossing element induces an automorphism
of S taking C_S(K) to a disjoint subgroup. These are the earlier reductions
2.5.5, 2.5.11, 2.5.18, K = K₀, and the action quotient from 2.5.21.
The section assembly owns their construction.

The intrinsic centralizer theorem forces C_J(K) into S; the supplement then
collapses to H = J. The rank bound is obtained from the SQTK hypothesis of J.
Neither the later rank-one setup nor the terminal construction setup is used.
The separate relative-centralizer transport applies the checked Sylow
centralizer theorem to a nonidentity inner involution in the actual image.
-/

public section

open Subgroup
open AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The full equality H = C_G(t), from the earlier source inputs only.
The kernel and Sylow image are constructed from conjugation on K. -/
theorem centralizer_eq_of_earlier_source (hG : IsSimpleQTKE κ G)
    (t : G) (ht : orderOf t = 2) (H : Subgroup G)
    (K : Subgroup (centralizer ({t} : Set G))) [K.Normal]
    (e : K ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 (centralizer ({t} : Set G)))
    (hH : H = (K ⊔ (S : Subgroup (centralizer ({t} : Set G)))).map
      (centralizer ({t} : Set G)).subtype)
    (hgen : K ⊔ (S : Subgroup (centralizer ({t} : Set G))) ⊔
      centralizer (K : Set (centralizer ({t} : Set G))) = ⊤)
    (hchar : centralizer (pCore 2 (centralizer (K : Set (centralizer ({t} : Set G)))) :
      Set (centralizer (K : Set (centralizer ({t} : Set G))))) ≤
      pCore 2 (centralizer (K : Set (centralizer ({t} : Set G)))))
    (hsurj : Function.Surjective (conjugationAction K e))
    (a : MulAut S)
    (hd : Disjoint ((centralizer (K : Set (centralizer ({t} : Set G)))).subgroupOf S)
      (((centralizer (K : Set (centralizer ({t} : Set G)))).subgroupOf S).map a.toMonoidHom)) :
    H = centralizer ({t} : Set G) := by
  have hr : primeRank 3 (centralizer ({t} : Set G)) ≤ 2 :=
    (hG.involution_centralizer_sqtk ht).stronglyQuasithin 3 Nat.prime_three (by decide)
  have hg := generated_eq_top_of_centralizer_supplement K e S hr hchar hsurj a hd hgen
  rw [hH, hg, ← MonoidHom.range_eq_map, range_subtype]

/-- The second clause C_H(z) = S, in ambient subgroup notation, when z
centralizes S and its actual action is an inner involution. The source
center identities supply precisely these inputs. -/
theorem relative_centralizer_eq_sylow_of_inner_image
    (H : Subgroup G) (f : H →* AutA6) (hf : Function.Surjective f)
    (S : Sylow 2 H) (hker : f.ker ≤ (S : Subgroup H)) (z : H)
    (hz : (S : Subgroup H) ≤ centralizer ({z} : Set H))
    (ho : orderOf (f z) = 2) (hi : f z ∈ AlternatingSix.ShadowLocal.inner) :
    H ⊓ centralizer ({(z : G)} : Set G) = (S : Subgroup H).map H.subtype := by
  have he := centralizer_eq_sylow_of_inner_image f hf S hker z hz ho hi
  have hrel : (centralizer ({(z : G)} : Set G)).subgroupOf H =
      centralizer ({z} : Set H) := by
    ext h
    simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro hh
      apply Subtype.ext
      exact hh
    · intro hh
      exact congrArg Subtype.val hh
  rw [← he, ← hrel, subgroupOf_map_subtype, inf_comm]

end CFSG.Quasithin.Chapter2.A6Shadow
