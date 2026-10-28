module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.SuzukiContainment
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!+# Removing two-group extensions after Ree recognition

The source recognition step in F.1.12 first gives an extension of a Lie
amalgam. In the Ree case every automorphism of two-power order is inner.
Consequently a normal Ree subgroup containing its centralizer contains
every two-subgroup of the extension. A two-group quotient then forces the
extension to equal its Ree subgroup. When that subgroup is F*, the
centralizer condition follows from the generalized Fitting theorem.

The final theorem applies this to the original source parabolic. Its
marking identifies only the intersection with the normal Ree subgroup,
under the given group isomorphism. Extension elimination upgrades this to
an isomorphism of the full parabolic; the existing residual argument then
puts the original S in the original Suzuki factor. The binary parameter
is excluded by that factor's nonsolvable Suzuki quotient.

This proves the extension-elimination step, including the literal source
transport. Existence of the recognized extension and its marked parabolic
intersection remains an explicit hypothesis, to be established from F.1.1.
No comparison with DGS85 Hypothesis A or exhaustive recognition is claimed.

Source: Aschbacher--Smith, F.1.12, printed pp.263--264,
especially the finite extension G-bar with F*(G-bar) of Lie type.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.SuzukiContainment

variable {X : Type*} [Group X] {N : Subgroup X} [N.Normal] {k : ℕ}

/-- A self-centralizing normal Ree subgroup absorbs every ambient two-subgroup.
This uses automorphisms of arbitrary two-power order, not just involutions. -/
theorem two_subgroup_le_ree_normal
    (e : N ≃* ReeF4.Model k) (hC : centralizer (N : Set X) ≤ N)
    (U : Subgroup X) (hU : IsPGroup 2 U) : U ≤ N := by
  intro x hx
  obtain ⟨r, hr⟩ := hU ⟨x, hx⟩
  have hxpow : x ^ (2 ^ r) = 1 := congrArg (fun u : U => (u : X)) hr
  let a : MulAut N := MulAut.conjNormal x
  have ha : a ^ (2 ^ r) = 1 := by
    change (MulAut.conjNormal x : MulAut N) ^ (2 ^ r) = 1
    rw [← map_pow, hxpow, map_one]
  have he : MulAut.congr e a ^ (2 ^ r) = 1 := by
    rw [← map_pow, ha, map_one]
  obtain ⟨g, hg⟩ := GreenBook.LieModels.ReeFour.twoPower_automorphism_inner k
    (MulAut.congr e a) r he
  obtain ⟨n, hn⟩ := (MulAut.congr_inner_iff e a).mp ⟨g, hg.symm⟩
  have hi : x ∈ (MulAut.innerSubgroup N).comap MulAut.conjNormal := ⟨n, hn.symm⟩
  rw [MulAut.conjNormal_comap_innerSubgroup] at hi
  exact (sup_le le_rfl hC) hi

/-- The actual quotient convention is X/N: a finite two-group extension
of a self-centralizing normal Ree subgroup is trivial. -/
theorem ree_two_extension_eq_top [Finite X]
    (e : N ≃* ReeF4.Model k) (hC : centralizer (N : Set X) ≤ N)
    (hQ : IsPGroup 2 (X ⧸ N)) : N = ⊤ := by
  let U : Sylow 2 X := default
  have hU : (U : Subgroup X) ≤ N := two_subgroup_le_ree_normal e hC U U.isPGroup'
  simpa only [sup_eq_right.mpr hU] using U.sup_eq_top_of_quotient_isPGroup N hQ

/-- The F* identification in the recognized source extension supplies
self-centralization, with no separate faithfulness assumption. -/
theorem ree_generalizedFitting_two_extension_eq_top [Finite X]
    (e : N ≃* ReeF4.Model k) (hF : generalizedFitting X = N)
    (hQ : IsPGroup 2 (X ⧸ N)) : N = ⊤ :=
  ree_two_extension_eq_top e (hF ▸ centralizer_generalizedFitting_le X) hQ

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Containment after recognition of a Ree extension. Only the intersection
of the transported parabolic with F* is marked; the two-group extension,
full-parabolic isomorphism, and positive Ree parameter are discharged here. -/
theorem sylow_le_suzuki_of_ree_extension [Finite X]
    (h : HypothesisF11 L S) (i : Fin 2) {m : ℕ} (hm : 1 ≤ m)
    (f : (L i ⧸ pCore 2 (L i)) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (e : N ≃* ReeF4.Model k) (hF : generalizedFitting X = N)
    (hQ : IsPGroup 2 (X ⧸ N)) (P : Subgroup X)
    (eP : parabolic L S i ≃* P)
    (hP : (P.subgroupOf N).map e.toMonoidHom = ReeF4.Parabolics.parabolic k .suzuki) :
    S ≤ L i := by
  have hN : N = ⊤ := ree_generalizedFitting_two_extension_eq_top e hF hQ
  have hPN : P ≤ N := hN ▸ le_top
  let d : P ≃* ReeF4.Parabolics.parabolic k .suzuki :=
    (subgroupOfEquivOfLe hPN).symm.trans
      (((P.subgroupOf N).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hP))
  exact sylow_le_suzuki_of_ree_parabolic h i hm f (eP.trans d)

end CFSG.Quasithin.ChapterF.Source.SuzukiContainment
