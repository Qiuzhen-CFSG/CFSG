module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.ModelAdapters
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Centralizer

/-!
# The conditional terminal A₆ shadow contradiction

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, printed pp.569–570, after Lemma 2.5.27.

The genuine construction gives E₁₆ with the local normalizer pair and the
required two-part bound. Its crossing representative is x*s, as returned by
the construction. Superscript-star maximality puts its normalizer in Γ*.
The specified nonidentity z belongs both to E₁₆ and to the ambient Sylow
center. The explicit central-intersection clause 1.1.4(3) therefore puts the
normalizer in He, contradicting Γe₀ = ∅.

All four finite-model premises are discharged by ModelAdapters. The final
bridge proves the full centralizer premise from the independent earlier-source
argument in Centralizer before applying this construction. No later setup is
used in the proof of that earlier theorem.

These theorems remain conditional on Construction.Setup, which contains the
later conclusions 2.5.23, 2.5.25 and 2.5.27. They do not claim to prove those
lemmas or the complete source elimination. The shadow assembly must construct
that setup; the Section 2.5 assembly owns the explicit 1.1.4(3) premise.
-/

public section

namespace CFSG.Quasithin.Chapter2.A6Shadow

open Subgroup A6ShadowConstruction

universe u
variable {G : Type u} [Group G] [Finite G]

/-- Construct a member of Γe₀ from the E₁₆ local pair and the exact central-intersection premise. -/
theorem gammaEvenZero_nonempty_of_terminal_source
    (d : Setup G) (hH : d.H ∈ gammaStar (Chapter1.He G) d.M)
    (hC : centralizer ({d.t} : Set G) ≤ d.H)
    (hzT : d.z ∈ (center d.T).map d.T.subtype) (hz1 : d.z ≠ 1)
    (h114 : ∀ A : Subgroup G, A ≠ ⊥ → IsPGroup 2 A →
      (center d.T).map d.T.subtype ⊓ A ≠ ⊥ → A ∈ Chapter1.S2e G) :
    (gammaEvenZero (Chapter1.He G) d.M).Nonempty := by
  obtain ⟨V, s, E, e, h⟩ := d.exists_terminal_pair_of_source
    (coreModelGeometry _) fusionModelFacts actionNormalizerModelFacts (reflectionOrbit _) hC
  dsimp only at h
  rcases h with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, hAne, hAp, hzA, _, _, hIN, hpair, hmax, hUT, hxT, hxU, _, _, hsize⟩
  let y := d.x * (s : G)
  let A := E ⊔ conjugate y E
  have hstar : normalizer (A : Set G) ∈ gammaStar (Chapter1.He G) d.M :=
    normalizer_mem_gammaStar_of_crossing_element hH d.sylow A d.T hAne hAp d.twoT
      hpair hmax (le_sup_left.trans hIN) hUT hxT.1 hxT.2 hxU hsize
  have hinter : (center d.T).map d.T.subtype ⊓ A ≠ ⊥ := by
    intro heq
    exact hz1 (show d.z ∈ (⊥ : Subgroup G) from heq ▸ ⟨hzT, hzA⟩)
  have hHe := (h114 A hAne hAp hinter).2.2
  exact ⟨normalizer (A : Set G), Or.inl hstar, hHe⟩

/-- The terminal contradiction, retaining the later setup and full-centralizer input explicitly. -/
theorem false_of_terminal_source
    (d : Setup G) (hH : d.H ∈ gammaStar (Chapter1.He G) d.M)
    (hempty : gammaEvenZero (Chapter1.He G) d.M = ∅)
    (hC : centralizer ({d.t} : Set G) ≤ d.H)
    (hzT : d.z ∈ (center d.T).map d.T.subtype) (hz1 : d.z ≠ 1)
    (h114 : ∀ A : Subgroup G, A ≠ ⊥ → IsPGroup 2 A →
      (center d.T).map d.T.subtype ⊓ A ≠ ⊥ → A ∈ Chapter1.S2e G) : False := by
  have h := gammaEvenZero_nonempty_of_terminal_source d hH hC hzT hz1 h114
  rw [hempty] at h
  exact Set.not_nonempty_empty h

/-- Discharge the construction's full-centralizer premise by the earlier-source
proof. Only the independent terminal setup and the declared earlier-source
and central-intersection inputs remain. -/
theorem false_of_earlier_source_and_terminal_setup
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G) (d : Setup G)
    (K : Subgroup (centralizer ({d.t} : Set G))) [K.Normal]
    (e : K ≃* alternatingGroup (Fin 6))
    (S : Sylow 2 (centralizer ({d.t} : Set G)))
    (hH : d.H = (K ⊔ (S : Subgroup (centralizer ({d.t} : Set G)))).map
      (centralizer ({d.t} : Set G)).subtype)
    (hgen : K ⊔ (S : Subgroup (centralizer ({d.t} : Set G))) ⊔
      centralizer (K : Set (centralizer ({d.t} : Set G))) = ⊤)
    (hchar : centralizer (pCore 2 (centralizer (K : Set (centralizer ({d.t} : Set G)))) :
      Set (centralizer (K : Set (centralizer ({d.t} : Set G))))) ≤
      pCore 2 (centralizer (K : Set (centralizer ({d.t} : Set G)))))
    (hsurj : Function.Surjective (AlternatingSix.ShadowLocal.conjugationAction K e))
    (a : MulAut S)
    (hd : Disjoint ((centralizer (K : Set (centralizer ({d.t} : Set G)))).subgroupOf S)
      (((centralizer (K : Set (centralizer ({d.t} : Set G)))).subgroupOf S).map a.toMonoidHom))
    (hGamma : d.H ∈ gammaStar (Chapter1.He G) d.M)
    (hempty : gammaEvenZero (Chapter1.He G) d.M = ∅)
    (hzT : d.z ∈ (center d.T).map d.T.subtype) (hz1 : d.z ≠ 1)
    (h114 : ∀ A : Subgroup G, A ≠ ⊥ → IsPGroup 2 A →
      (center d.T).map d.T.subtype ⊓ A ≠ ⊥ → A ∈ Chapter1.S2e G) : False := by
  have ht : orderOf d.t = 2 := orderOf_eq_prime d.t_square d.t_ne_one
  have hC := centralizer_eq_of_earlier_source hG d.t ht d.H K e S hH hgen hchar hsurj a hd
  exact false_of_terminal_source d hGamma hempty hC.ge hzT hz1 h114

end CFSG.Quasithin.Chapter2.A6Shadow
