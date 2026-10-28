module

public import Stellmacher.SectionFiveToSeven.SixOneCrossNormalizers
public import Stellmacher.SectionFiveToSeven.PFamilyConjugation
public import Stellmacher.BaumannNormalizer
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# The orbit normalizer in Stellmacher (6.1)

Under Hypothesis 2 with `S = S₀`, let `E` have shared Sylow subgroup
`B=B(S)` and satisfy `E ∨ S = P₁`. Let `L` be the actual P₁-conjugate
closure of B. Suppose nontrivial `W₁ ≤ B` is normalized by L and equals
`[Ω₁(Z(B)), O²(E)]`. If U normalizes B and E normalizes the actual orbit
closure `W=⟨W₁^U⟩`, then L normalizes W.

The proof makes the source's two applications of (5.4) and (3.9) explicit.
The closure W is a nontrivial 2-subgroup of B, normalized by E and U,
hence by every Eᵘ. It therefore lies in the 2-core of E ∨ Eᵘ, and the
cross-normalizer theorem shows that Eᵘ normalizes W₁. For s in S, Eˢ lies
in L and also normalizes W₁. Thus W₁ gives a nontrivial 2-core in Eˢ ∨ Eᵘ.
A second cross-normalizer application shows that Eˢ normalizes W₁ᵘ, using
conjugation covariance of the omega center and residual. Every Eˢ therefore
normalizes W.

Finally, C=⟨E^S⟩ is normalized by S and by its subgroup E. Since E ∨ S=P₁,
P₁ normalizes C; since B≤E≤C, the defining closure L lies in C. This proves
the required normalization of W. Each core argument takes place in its
actual two-generator join, with no ambient generation assumption.

Source: Stellmacher (6.1), Journal of Algebra 190 (1997), p.30, the
sentence applying (5.4) and (3.9), in `refs/latex/stellmacher-n-group.tex`.
No Hall or odd-order hypothesis on U is needed here: the separate orbit
stage uses those assumptions to supply the explicit E-normalization input.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem le_conjugateClosure {G : Type*} [Group G] (X A : Subgroup G) :
    X ≤ conjugateClosure X A := by
  intro x hx
  exact Subgroup.subset_closure ⟨1, ⟨x, hx⟩, by simp⟩

private theorem conjugate_le_closure {G : Type*} [Group G]
    (X A : Subgroup G) (a : G) (ha : a ∈ A) :
    conjugateBy X a ≤ conjugateClosure X A := by
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.subset_closure ⟨⟨a, ha⟩, ⟨x, hx⟩, rfl⟩

private theorem actors_normalize_closure {G : Type*} [Group G]
    (X A : Subgroup G) : A ≤ Subgroup.normalizer (conjugateClosure X A : Set G) := by
  rw [conjugateClosure, Subgroup.le_normalizer_closure_iff]
  intro a ha x hx
  obtain ⟨b, w, rfl⟩ := hx
  apply Subgroup.subset_closure
  refine ⟨⟨a * (b : G), A.mul_mem ha b.property⟩, w, ?_⟩
  change a * ((b : G) * (w : G) * (b : G)⁻¹) * a⁻¹ =
    (a * (b : G)) * (w : G) * (a * (b : G))⁻¹
  group

private theorem closure_le_normalized {G : Type*} [Group G]
    (X A B : Subgroup G) (hXB : X ≤ B)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) : conjugateClosure X A ≤ B := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨a, x, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hAB a.property) (x : G)).mp (hXB x.property)

private theorem conjugate_normalizes {G : Type*} [Group G]
    (E W : Subgroup G) (hEW : E ≤ Subgroup.normalizer (W : Set G))
    (u : G) (hu : u ∈ Subgroup.normalizer (W : Set G)) :
    conjugateBy E u ≤ Subgroup.normalizer (W : Set G) := by
  have hm := Subgroup.map_mono (f := (MulAut.conj u).toMonoidHom) hEW
  have hWmap : W.map (MulAut.conj u).toMonoidHom = W :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hu
  rw [Subgroup.map_equiv_normalizer_eq, hWmap] at hm
  exact hm

private theorem core_ne_bot_of_normalized {G : Type*} [Group G]
    (J X : Subgroup G) (hXne : X ≠ ⊥) (hXp : IsPGroup 2 X)
    (hXJ : X ≤ J) (hJN : J ≤ Subgroup.normalizer (X : Set G)) :
    twoCoreIn J ≠ ⊥ := by
  have hXnormal : (X.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXJ).mpr hJN
  have hXJp : IsPGroup 2 (X.subgroupOf J) :=
    hXp.comap_of_injective J.subtype J.subtype_injective
  have hXcore : X ≤ twoCoreIn J := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hXJ]
    exact Subgroup.map_mono (show X.subgroupOf J ≤ pCore 2 J from le_sSup ⟨hXnormal, hXJp⟩)
  intro hbot
  exact hXne (le_bot_iff.mp (hXcore.trans_eq hbot))

public theorem sixOne_hall_orbit_normalizer
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) (hS : S = (S0 : Subgroup H))
    (E U W1 M : Subgroup H)
    (hE : E ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hEL : E ≤ sectionSixL (baumannIn S) P1)
    (hgen : E ⊔ S = P1)
    (hUB : U ≤ Subgroup.normalizer (baumannIn S : Set H))
    (hW1B : W1 ≤ baumannIn S) (hW1ne : W1 ≠ ⊥)
    (hW1 : W1 = ⁅omegaOneCenter (baumannIn S), twoResidualIn E⁆)
    (hLW1 : sectionSixL (baumannIn S) P1 ≤ Subgroup.normalizer (W1 : Set H))
    (hEW : E ≤ Subgroup.normalizer (conjugateClosure W1 U : Set H))
    (hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M) :
    sectionSixL (baumannIn S) P1 ≤
      Subgroup.normalizer (conjugateClosure W1 U : Set H) := by
  classical
  let B := baumannIn S
  let L := sectionSixL B P1
  let W := conjugateClosure W1 U
  have hBS : B ≤ S := inf_le_left
  have hBp : IsPGroup 2 B := S0.isPGroup'.to_le (hBS.trans_eq hS)
  have hBE : B ≤ E := hE.1.2.1.1
  have hSP1 : S ≤ P1 := by rw [← hgen]; exact le_sup_right
  have hSB : S ≤ Subgroup.normalizer (B : Set H) :=
    S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hP1L : P1 ≤ Subgroup.normalizer (L : Set H) :=
    actors_normalize_closure B P1
  have hUW : U ≤ Subgroup.normalizer (W : Set H) := actors_normalize_closure W1 U
  have hWB : W ≤ B := closure_le_normalized W1 U B hW1B hUB
  have hWne : W ≠ ⊥ := by
    intro hbot
    exact hW1ne (le_bot_iff.mp ((le_conjugateClosure W1 U).trans_eq hbot))
  have hWp : IsPGroup 2 W := hBp.to_le hWB
  have hW1p : IsPGroup 2 W1 := hBp.to_le hW1B
  have hEufamily (u : U) : conjugateBy E (u : H) ∈ PFamily (⊤ : Subgroup H) B :=
    (conjugateBy_mem_pFamily_iff B E u (hUB u.property)).mpr hE
  have hEuW1 (u : U) : conjugateBy E (u : H) ≤ Subgroup.normalizer (W1 : Set H) := by
    have hEuW : conjugateBy E (u : H) ≤ Subgroup.normalizer (W : Set H) :=
      conjugate_normalizes E W hEW u (hUW u.property)
    have hcore := core_ne_bot_of_normalized (E ⊔ conjugateBy E (u : H)) W hWne hWp
      (hWB.trans (hBE.trans le_sup_left)) (sup_le hEW hEuW)
    have hn := (sixOne_cross_normalizers S0 S P1 P2 h hS E (conjugateBy E (u : H)) M
      hE (hEufamily u) hM hcore).1
    rwa [← hW1] at hn
  have hEsfamily (s : S) : conjugateBy E (s : H) ∈ PFamily (⊤ : Subgroup H) B :=
    (conjugateBy_mem_pFamily_iff B E s (hSB s.property)).mpr hE
  have hEsL (s : S) : conjugateBy E (s : H) ≤ L := by
    have hm := Subgroup.map_mono (f := (MulAut.conj (s : H)).toMonoidHom) hEL
    have hLm : L.map (MulAut.conj (s : H)).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP1L (hSP1 s.property))
    change (conjugateBy E (s : H)) ≤ L.map (MulAut.conj (s : H)).toMonoidHom at hm
    rwa [hLm] at hm
  have hWu (u : U) : conjugateBy W1 (u : H) =
      ⁅omegaOneCenter B, twoResidualIn (conjugateBy E (u : H))⁆ := by
    have hBmap : B.map (MulAut.conj (u : H)).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUB u.property)
    have hOmap : (omegaOneCenter B).map (MulAut.conj (u : H)).toMonoidHom = omegaOneCenter B := by
      change (omegaOneCenterAmbient B).map _ = omegaOneCenterAmbient B
      rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj (u : H)).injective, hBmap]
    have hRmap : (twoResidualIn E).map (MulAut.conj (u : H)).toMonoidHom =
        twoResidualIn (conjugateBy E (u : H)) :=
      map_twoResidualAmbient_of_subgroup_image E (MulAut.conj (u : H)).toMonoidHom _ rfl
    change W1.map (MulAut.conj (u : H)).toMonoidHom = _
    have hW1' : W1 = ⁅omegaOneCenter B, twoResidualIn E⁆ := hW1
    rw [hW1', Subgroup.map_commutator, hOmap, hRmap]
  have hEsWu (s : S) (u : U) : conjugateBy E (s : H) ≤
      Subgroup.normalizer (conjugateBy W1 (u : H) : Set H) := by
    have hcore := core_ne_bot_of_normalized
      (conjugateBy E (s : H) ⊔ conjugateBy E (u : H)) W1 hW1ne hW1p
      (hW1B.trans ((hEsfamily s).1.2.1.1.trans le_sup_left))
      (sup_le ((hEsL s).trans hLW1) (hEuW1 u))
    have hn := (sixOne_cross_normalizers S0 S P1 P2 h hS
      (conjugateBy E (s : H)) (conjugateBy E (u : H)) M
      (hEsfamily s) (hEufamily u) hM hcore).2
    rwa [← hWu u] at hn
  have hEsW (s : S) : conjugateBy E (s : H) ≤ Subgroup.normalizer (W : Set H) := by
    rw [show W = conjugateClosure W1 U from rfl, conjugateClosure, Subgroup.le_normalizer_closure_iff]
    intro e he x hx
    obtain ⟨u, w, rfl⟩ := hx
    apply conjugate_le_closure W1 U u u.property
    apply (Subgroup.mem_normalizer_iff.mp (hEsWu s u he) _).mp
    exact ⟨w, w.property, rfl⟩
  let C := conjugateClosure E S
  have hCW : C ≤ Subgroup.normalizer (W : Set H) := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨s, e, rfl⟩
    exact hEsW s ⟨e, e.property, rfl⟩
  have hEC : E ≤ C := le_conjugateClosure E S
  have hP1C : P1 ≤ Subgroup.normalizer (C : Set H) := by
    rw [← hgen]
    exact sup_le (hEC.trans C.le_normalizer) (actors_normalize_closure E S)
  have hLC : L ≤ C := closure_le_normalized B P1 C (hBE.trans hEC) hP1C
  exact hLC.trans hCW

end Stellmacher.SectionsFiveToSeven
