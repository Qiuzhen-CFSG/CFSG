module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentFullSixAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalProductWeight

/-!
# Original centralizer amalgams at both escaping weights

The tetrahedral orbit calculation excludes the product commutator bound
at weight two. Apply this to the constructed ordinary A₆ centralizer pair:
its join is therefore N_G(J(T)), is maximal two-local, has the actual
L₃(2) quotient, and has a unique outside parabolic.

For two escaping vectors of weights two and four, the marked Sylow action
identifies their original invariant planes, so both joins use the same
literal B=L₂T. Their outside parabolics are distinct because their fixed
lines on V∩Ω₁Z(T) are distinct. They cannot both lie in N_G(J(T)); hence
the weight-four join takes the product alternative. Its commutator bound
and the actual Sylow supplement give B≤N_G(O²(P₄)).

This supplies the first comparison in 13.4.12 when both selected components
have ordinary A₆ quotients. The linear-three rows, the application of
13.4.7 to the pair P₂,P₄, the remaining module-weight clauses, and the
reciprocal commutator and graph arguments remain obligations. The genuine
earlier Chapter12/13.3 and PlaneAmalgamSource1347 inputs remain explicit;
the independent LargeDistanceInput is still needed for the linear-three
rows. A nonsolvable centralizer at only one selected weight is insufficient
for the final source theorem.

Source: Aschbacher–Smith 13.4.10(8) and 13.4.12, printed pp.909–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original ordinary A₆ pair has weight four in the product
alternative; the linear alternative retains its full normalizer geometry. -/
theorem ordinary_six_original_weight_amalgam
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ≤ centralizer ({z.val} : Set G) ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X := P ⊔ B
        let K₂ := (pResidual 2 P).map P.subtype
        let L₂ := (pResidual 2 B).map B.subtype
        X ∈ Chapter1.HOver G (T : Set G) ∧
        ((⁅K₂,L₂⁆ ≤ K₂.pCoreIn 2 ∧ m.weight z = 4) ∨
          (Solvable.LinearAmalgamConclusion T X ∧
            X = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
            IsMaximalTwoLocal X ∧
            Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL) ∧
            (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
              Q ≤ X → Q = P))) := by
  obtain ⟨W,hW,hT,P,hP,hPH,hlocal,halt⟩ := ordinary_six_original_amalgam
    h₀ h structural modules D m h1332 fixed hindex hM h1347
    z hzT hzL hK hHN hKM hfK eK
  refine ⟨W,hW,hT,P,hP,hPH,hlocal,?_⟩
  rcases halt with hprod | hlinear
  · exact Or.inl ⟨hprod,original_product_weight_four h structural D m W hW hT P hP
      z hzL hPH hprod⟩
  · exact Or.inr hlinear

/-- At weight two the original join is necessarily the maximal
Thompson normalizer, with its literal quotient and unique outside parabolic. -/
theorem ordinary_six_weight_two_thompson
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hweight : m.weight z = 2) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ≤ centralizer ({z.val} : Set G) ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X := P ⊔ B
        X ∈ Chapter1.HOver G (T : Set G) ∧
        (Solvable.LinearAmalgamConclusion T X ∧
            X = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
            IsMaximalTwoLocal X ∧
            Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL) ∧
            (∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
              Q ≤ X → Q = P)) := by
  obtain ⟨W,hW,hT,P,hP,hPH,hlocal,halt⟩ := ordinary_six_original_weight_amalgam
    h₀ h structural modules D m h1332 fixed hindex hM h1347
    z hzT hzL hK hHN hKM hfK eK
  refine ⟨W,hW,hT,P,hP,hPH,hlocal,?_⟩
  exact halt.resolve_left (fun hh => by omega)

/-- The full original Sylow subgroup preserves exactly one natural plane. -/
theorem original_invariant_plane_unique
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W₁ W₂ : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW₁ : Module.finrank (ZMod 2) W₁ = 2)
    (hW₂ : Module.finrank (ZMod 2) W₂ = 2)
    (hT₁ : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W₁ : Set G))
    (hT₂ : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W₂ : Set G)) : W₁ = W₂ := by
  let X := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  obtain ⟨S,hS⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_subgroupOf_eq_of_normal N
  let e := subgroupOfEquivOfLe (show L ≤ X from le_sup_left)
  let q : N →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp ((QuotientGroup.mk' (centralCore L)).comp e.toMonoidHom)
  have hq : Function.Surjective q := m.quotient.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp e.surjective)
  let P := S.mapSurjective hq
  have hi (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
      (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G)) :
      ∀ a ∈ (P : Subgroup (alternatingGroup (Fin 6))).map
        (alternatingGroup (Fin 6)).subtype, move a W = W := by
    rintro a ⟨b,⟨c,hc,rfl⟩,rfl⟩
    have hcT : c.val.val ∈ (T : Subgroup G) := by rw [hS] at hc; exact hc
    exact (BinaryFlags.NaturalPairing.mem_stabilizer_iff_map W _).mp
      ((m.normalizes_naturalPreimage_iff W (e c)).mp (hT hcT))
  obtain ⟨g,hg⟩ := exists_conjugate_T0_le (alternatingGroup (Fin 6)) le_rfl P
  have he₁ := (invariant_unique_conjugate T0 le_rfl g.val W₁
    (fun a ha => hi W₁ hT₁ a (hg ha))).2 hW₁
  have he₂ := (invariant_unique_conjugate T0 le_rfl g.val W₂
    (fun a ha => hi W₂ hT₂ a (hg ha))).2 hW₂
  exact he₁.trans he₂.symm

/-- Outside parabolics at distinct escaping weights have different fixed lines. -/
theorem different_weight_parabolics
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z w : V) (hz : m.weight z = 2) (hw : m.weight w = 4)
    (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (P Q : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hQ : Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPz : P ≤ centralizer ({z.val} : Set G))
    (hQw : Q ≤ centralizer ({w.val} : Set G)) : P ≠ Q := by
  classical
  have hz1 : z ≠ 1 := by intro he; rw [he,m.weight_one] at hz; omega
  have hw1 : w ≠ 1 := by intro he; rw [he,m.weight_one] at hw; omega
  intro he
  have hp := m.central_four_fixed_of_escape h structural z hz1 hzT P hPz hP.1.2
  have hq := m.central_four_fixed_of_escape h structural w hw1 hwT Q hQw hQ.1.2
  have hlines : zpowers z.val = zpowers w.val := by rw [←hp,←hq,he]
  have hm : z.val ∈ zpowers w.val := hlines ▸ mem_zpowers z.val
  let := D.elementary
  have ho : orderOf w.val = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian w.val w.property)
    (fun he => hw1 (Subtype.ext he))
  rw [mem_zpowers_iff_mem_range_orderOf,ho] at hm
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · exact hz1 (Subtype.ext (by simpa using he.symm))
  · have hzw : z = w := Subtype.ext (by simpa using he.symm)
    rw [hzw,hw] at hz
    omega

/-- At the two actual escaping weights in ordinary A₆ component rows,
the weight-two join is the Thompson normalizer, while the weight-four
join necessarily has the product commutator bound. -/
theorem ordinary_six_both_weights_comparison
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (h1347 : Solvable.PlaneAmalgamSource1347 D m)
    (z w : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hwL : w.val ∉ centralizer (L : Set G))
    (hz : m.weight z = 2) (hw : m.weight w = 4)
    (K N : Subgroup G)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hN : N ∈ Chapter1.cComponentsIn (centralizer ({w.val} : Set G)))
    (hNN : centralizer ({w.val} : Set G) ≤ normalizer (N : Set G))
    (hNM : ¬ N ≤ normalizer (L : Set G))
    (hfN : N ∈ MainForward.faithfulLocalComponents T)
    (eN : (N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6)) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      ∃ P Q : Subgroup G,
        P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
        P ≤ centralizer ({z.val} : Set G) ∧ Q ≤ centralizer ({w.val} : Set G) ∧ P ≠ Q ∧
        let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
        let X₂ := P ⊔ B
        let R₄ := (pResidual 2 Q).map Q.subtype
        let L₂ := (pResidual 2 B).map B.subtype
        X₂ = normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        IsMaximalTwoLocal X₂ ∧ Nonempty ((X₂ ⧸ pCore 2 X₂) ≃* Matrix.PSL3Two.SL) ∧
        (∀ U ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)), U ≤ X₂ → U = P) ∧
        Q ⊔ B ∈ Chapter1.HOver G (T : Set G) ∧ ⁅R₄,L₂⁆ ≤ R₄.pCoreIn 2 ∧
        B ≤ normalizer (R₄ : Set G) := by
  obtain ⟨W₂,hW₂,hT₂,P,hP,hPz,_,_,hX₂,hmax,hquot,hunique⟩ :=
    ordinary_six_weight_two_thompson h₀ h structural modules D m h1332 fixed hindex hM h1347
      z hzT hzL hK hKN hKM hfK eK hz
  obtain ⟨W₄,hW₄,hT₄,Q,hQ,hQw,hlocal,halt⟩ :=
    ordinary_six_original_weight_amalgam h₀ h structural modules D m h1332 fixed hindex hM h1347
      w hwT hwL hN hNN hNM hfN eN
  have hWe := original_invariant_plane_unique D m W₂ W₄ hW₂ hW₄ hT₂ hT₄
  subst W₄
  have hne := different_weight_parabolics h structural D m z w hz hw hzT hwT P Q hP hQ hPz hQw
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W₂ : Set G)
  let R := (pResidual 2 Q).map Q.subtype
  let L₂ := (pResidual 2 B).map B.subtype
  have hcomm : ⁅R,L₂⁆ ≤ R.pCoreIn 2 := by
    rcases halt with hprod | ⟨_,hX₄,_,_,_⟩
    · exact hprod.1
    · exfalso
      apply hne
      apply (hunique Q hQ ?_).symm
      rw [hX₂,←hX₄]
      exact le_sup_left
  refine ⟨W₂,hW₂,hT₂,P,Q,hP,hQ,hPz,hQw,hne,hX₂,hmax,hquot,hunique,hlocal,hcomm,?_⟩
  have hTB : (T : Subgroup G) ≤ B := le_inf le_sup_right hT₂
  have hB : L₂ ⊔ (T : Subgroup G) = B :=
    embedded_pResidual_sup_of_common_sylow B T (T.subtype hTB)
      (by rw [T.coe_subtype,map_subgroupOf_eq_of_le hTB])
  change B ≤ normalizer (R : Set G)
  rw [←hB]
  exact sup_le (le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 R)))
    (hQ.1.1.2.trans (le_normalizer_embedded_pResidual 2 Q))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
