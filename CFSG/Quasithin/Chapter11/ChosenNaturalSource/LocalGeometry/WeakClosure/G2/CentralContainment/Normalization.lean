module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment.Transfer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots.Source

/-!
# Ambient recovery of the original G₂ covering center

Each reciprocal root action fixes C_(Vᵍ)(Lᵍ), so this elementary subgroup
centralizes the original root-centralizer span E. Since E has corank at most n,
the strict r-bound makes the subgroup normalize V, and m(V)=2n forces its
action on V to be trivial. When the covering center is nonzero, maximal-local
uniqueness and the checked equality V=V_M then make V normalize Vᵍ.
The full commutator contains C_V(L), which consequently lies in Vᵍ.
The zero-center branch needs only the trivial containment.

Source instantiates every actor and numerical premise using the checked
reciprocal-root source family. This recovers the central term without a
RootSpan.moved assumption or any assertion that C_V(L) vanishes.
Source: Aschbacher--Smith 11.0.3(3), 4.2.13 and 11.2.2(1,3,5),
printed pp.760,767--768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

private theorem marked_fixes_center (b : Model S.field.Carrier) (v : D.space)
    (hv : v ∈ Preliminary.centralSpace D) : Preliminary.markedAction D m b v = v := by
  exact (Preliminary.markedProjection_isCover D m).2.1
    ((Preliminary.markedProjection_ker D m).symm ▸ hv) b

private theorem large_fixed_centralizes (E B : Subgroup G) [IsElementaryAbelian 2 B]
    (hEV : E ≤ V) (hBC : B ≤ centralizer (E : Set G))
    (hcor : subgroupCorank V E ≤ S.field.degree)
    (hr : (2*S.field.degree : ℕ∞) < globalR V)
    (hm : @localM G _ V D.elementary = 2*S.field.degree) :
    B ≤ centralizer (V : Set G) := by
  let := D.elementary
  have hEr : (subgroupCorank V E : ℕ∞) < globalR V :=
    lt_of_le_of_lt (by exact_mod_cast (hcor.trans (by omega : S.field.degree ≤ 2*S.field.degree))) hr
  have hBN := hBC.trans (centralizer_le_normalizer_of_corank_lt_globalR hEV hEr)
  let := inducedAutomizer_elementary V B hBN
  apply (inducedAutomizer_eq_bot_iff hBN).mp
  apply _root_.eq_bot_iff.mpr
  intro b hb
  by_contra h1
  have hbne : b ≠ 1 := fun h => h1 (mem_bot.mpr h)
  have hi : orderOf b = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian b hb) hbne
  have hlow := moduleM_le_involution (automizerRepresentation V) hi
  have hhigh := fixedCodim_mono (automizerRepresentation V) (zpowers_le.mpr hb)
  rw [fixedCodim_inducedAutomizer V B hBN] at hhigh
  have hbound := ChapterE.Section06.subgroupCorank_antitone
    (V:=V) (le_inf hEV (le_centralizer_iff.mpr hBC))
  change localM V ≤ _ at hlow
  rw [hm] at hlow
  have hn := S.nonbinary
  omega

theorem root_span_centralizes_conjugate_center
    (g : G) (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (hroots : ∀ Z ∈ RootCentralizers.longRoots S.field.Carrier,
      Nonempty (ReciprocalRoots.RootData D S m g a Z)) :
    rootCentralizerSpan V (RootPullback.roots _ a) ≤
      centralizer ((V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom : Set G) := by
  apply iSup_le
  intro B
  apply iSup_le
  rintro ⟨Z,hZ,rfl⟩
  obtain ⟨r⟩ := hroots Z hZ
  intro x hx
  rintro _ ⟨y,hy,rfl⟩
  let v : V := ⟨y,hy.1⟩
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have hw : w ∈ Preliminary.centralSpace D :=
    (Preliminary.mem_centralSpace_iff D w).mpr (by
      dsimp only [w]
      rw [ofAdd_toAdd,MulEquiv.apply_symm_apply]
      exact hy.2)
  have hh := r.action ⟨x,hx⟩ w
  rw [marked_fixes_center D S m _ w hw] at hh
  simp only [w,v,ofAdd_toAdd,MulEquiv.apply_symm_apply] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm

/-- A nonzero covering center permits mutual normalization, using the full
reciprocal root family and the strict source r-bound. -/
theorem normalizes_conjugate_of_central_ne_bot
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hc : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hm : @localM G _ V D.elementary = 2*S.field.degree)
    (hr : (2*S.field.degree : ℕ∞) < globalR V)
    (g : G) (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (hact : ∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (hroots : ∀ Z ∈ RootCentralizers.longRoots S.field.Carrier,
      Nonempty (ReciprocalRoots.RootData D S m g a Z)) :
    V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  let := D.elementary
  let C := V ⊓ centralizer (L : Set G)
  let Cg := C.map (MulAut.conj g).toMonoidHom
  let E := rootCentralizerSpan V (RootPullback.roots _ a)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ V from inf_le_left)
  let : IsElementaryAbelian 2 Cg := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hEV : E ≤ V := iSup_le fun _ => iSup_le fun _ => inf_le_left
  have hEC := root_span_centralizes_conjugate_center D S m g a hroots
  have hCgV : Cg ≤ centralizer (V : Set G) :=
    large_fixed_centralizes D S E Cg hEV (le_centralizer_iff.mp hEC)
      (rootCentralizerSpan_corank_le D S m _ a hact) hr hm
  have hLC : L ≤ centralizer (C : Set G) := le_centralizer_iff.mp inf_le_right
  have hCM : centralizer (C : Set G) ≤ normalizer (L : Set G) :=
    (Subgroup.centralizer_le_normalizer _).trans
      (normalizer_le_of_unique_maximalTwoLocal hunique (IsElementaryAbelian.isPGroup 2 C)
        hc (hLC.trans (Subgroup.centralizer_le_normalizer _)))
  have hCNA : centralizer (Cg : Set G) ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom)
      (hCM.trans (Preliminary.normalizer_le_of_centralizer_ne_bot D S hc))
    rwa [Theory.GroupTheory.map_centralizer_equiv,map_equiv_normalizer_eq] at hh
  exact (le_centralizer_iff.mp hCgV).trans hCNA

/-- The missing central containment follows from the actual ambient source
hypotheses. The central kernel is never assumed trivial. -/
theorem central_le_conjugate
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hm : @localM G _ V D.elementary = 2*S.field.degree)
    (hr : (2*S.field.degree : ℕ∞) < globalR V)
    (g : G) (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (hact : ∀ (x : V.map (MulAut.conj g).toMonoidHom) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (ha : a.range = EvenTwoRank.elementary S.field.Carrier)
    (hroots : ∀ Z ∈ RootCentralizers.longRoots S.field.Carrier,
      Nonempty (ReciprocalRoots.RootData D S m g a Z)) :
    V ⊓ centralizer (L : Set G) ≤ V.map (MulAut.conj g).toMonoidHom := by
  by_cases hc : V ⊓ centralizer (L : Set G) = ⊥
  · rw [hc]
    exact bot_le
  · exact (central_le_full_commutator D S m _ a hact ha).trans
      (le_normalizer_iff_commutator_le_right.mp
        (normalizes_conjugate_of_central_ne_bot D S m hunique hc hm hr g a hact hroots))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment
