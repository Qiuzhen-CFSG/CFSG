module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ClassicalApplications
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.ClassicalNormality
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.NormalizedPerfect
public import Theory.GroupTheory.EquivariantParabolicLift
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.MarkedParabolicPair

/-!
# The two symplectic residuals in the original local family

An invariant marked parabolic fixes the symplectic diagram. Conjugate the
model once to match the original S-intersection to its standard Sylow.
Both incident parabolics are then invariant under the transported S-action.
Their full preimages and solvable residuals are S-normalized. Perfectness,
the actual SL₂ core quotients, and nontrivial two-cores establish all clauses
of the original family L(G₁,S).

The residuals are the literal constructions in K N_S(K), identified with
their pullbacks in K. `HigherSymplectic` supplies the marked parabolic from
C.2.7 and consumes both memberships in the original nonblock argument.
No general local-family Borel equality is assumed.
Source: Aschbacher--Smith 15.1.20(2), printed p.1095.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem quotient_marking_equivariant {X Y : Type*} [Group X] [Group Y]
    (N : Subgroup X) [N.Characteristic] (e : (X ⧸ N) ≃* Y)
    (b : MulAut X) (x : X) :
    e (QuotientGroup.mk' N (b x)) =
      MulAut.congr e (quotientAut N b) (e (QuotientGroup.mk' N x)) := by
  change e (QuotientGroup.mk' N (b x)) =
    e (quotientAut N b (e.symm (e (QuotientGroup.mk' N x))))
  rw [e.symm_apply_apply,quotientAut_apply_mk]

private theorem preserves_class_of_invariant {E : Type*} [Group E]
    (D P : Subgroup E) (a : MulAut E) (hD : D.map a.toMonoidHom = D)
    (g : E) (hP : D.map (MulAut.conj g).toMonoidHom = P) :
    ∃ x : E, P.map a.toMonoidHom = P.map (MulAut.conj x).toMonoidHom := by
  refine ⟨a g * g⁻¹,?_⟩
  rw [←hP]
  calc
    _ = (D.map a.toMonoidHom).map (MulAut.conj (a g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp
    _ = D.map (MulAut.conj (a g)).toMonoidHom := by rw [hD]
    _ = (D.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj (a g * g⁻¹)).toMonoidHom := by
      rw [map_map]
      congr 1
      ext x
      simp [mul_assoc]

open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

/-- A marked invariant parabolic fixes the symplectic diagram. After one
Sylow conjugation both literal parabolic residuals belong to the original
local family. The marking will be supplied by C.2.7 for the selected component. -/
theorem localFamily_symplectic_residual_members
    (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (a : d.NormalizerAction K)
    {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n)
    (e : d.normalizerImage K ≃* Sp F)
    (hm : ∃ g : Sp F,
      ((d.normalizerMarkedImage K).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = pointParabolic ∨
      ((d.normalizerMarkedImage K).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom = planeParabolic) :
    ∃ e' : d.normalizerImage K ≃* Sp F,
      ∀ P ∈ ({pointParabolic,planeParabolic} : Set (Subgroup (Sp F))),
        d.normalizerParabolicResidual K (P.map e'.symm.toMonoidHom) ∈ Chapter1.LIn d.G1 d.S := by
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hK.2
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
  let ec := (MulEquiv.ofBijective a.coreToImage
    (a.symplectic_four_core_bijective hq hfour e)).trans e
  have hnK := d.localFamily_symplectic_four_normalizes hG h hK hq ec
  obtain ⟨Q,hQ⟩ := ComponentModels.source20_sylow_intersection hK.2
  let q₀ := e.toMonoidHom.comp (d.toNormalizerImage K)
  have hq₀ : Function.Surjective q₀ := e.surjective.comp (d.toNormalizerImage_surjective K)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Sp F) (Q.mapSurjective hq₀)
    (unipotentSylow hF hn.le)
  let e' := e.trans (MulAut.conj g)
  let ec' := ec.trans (MulAut.conj g)
  let q := e'.toMonoidHom.comp (d.toNormalizerImage K)
  have hU : (Q : Subgroup K).map q = unipotent := by
    have hh := congrArg (fun U : Sylow 2 (Sp F) => (U : Subgroup (Sp F))) hg
    change ((Q : Subgroup K).map q₀).map (MulAut.conj g).toMonoidHom = unipotent at hh
    rw [map_map] at hh
    exact hh
  have hQL : (Q : Subgroup K) = (d.S ⊓ K).subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [map_subgroupOf_eq_of_le (show d.S ⊓ K ≤ K from inf_le_right)]
    exact hQ
  let α : d.S →* MulAut (Sp F) := (MulAut.congr ec').toMonoidHom.comp
    ((quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hnK)))
  have heq (s : d.S) (k : K) :
      q (K.normalizerMonoidHom (inclusion hnK s) k) = α s (q k) := by
    have hc (x : K) : q x = ec' (QuotientGroup.mk' (pCore 2 K) x) := rfl
    rw [hc,hc]
    exact quotient_marking_equivariant (pCore 2 K) ec'
      (K.normalizerMonoidHom (inclusion hnK s)) k
  have hnSK : d.S ≤ normalizer ((d.S ⊓ K) : Set G) :=
    (le_inf d.S.le_normalizer hnK).trans inf_normalizer_le_normalizer_inf
  have hUi (s : d.S) : unipotent.map (α s).toMonoidHom = unipotent := by
    have hh := EquivariantLift.map_invariant K q hnK α heq (D := d.S ⊓ K) hnSK s
    rw [←hQL,hU] at hh
    exact hh
  have hSM : d.S ≤ d.MZ := by
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    intro x hx
    exact ⟨d.S_le_G1 hx,hMc.2 (fun z hz =>
      (centralInvolutions_le_centralizer_sylow T hz x (d.S_le_T hx)).symm)⟩
  let D := (d.MZ.subgroupOf K).map q
  have hDi (s : d.S) : D.map (α s).toMonoidHom = D :=
    EquivariantLift.map_invariant K q hnK α heq (hSM.trans d.MZ.le_normalizer) s
  have hDm : ∃ x : Sp F,
      D.map (MulAut.conj x).toMonoidHom = pointParabolic ∨
      D.map (MulAut.conj x).toMonoidHom = planeParabolic := by
    obtain ⟨x,hx⟩ := hm
    refine ⟨x*g⁻¹,?_⟩
    have he : D.map (MulAut.conj (x*g⁻¹)).toMonoidHom =
        ((d.normalizerMarkedImage K).map e.toMonoidHom).map (MulAut.conj x).toMonoidHom := by
      change (((d.MZ.subgroupOf K).map _).map _) = _
      rw [map_map,normalizerMarkedImage,map_map,map_map]
      congr 1
      ext k
      simp [q,e',mul_assoc]
    rwa [he]
  have hpair (s : d.S) :
      pointParabolic.map (α s).toMonoidHom = pointParabolic ∧
      planeParabolic.map (α s).toMonoidHom = planeParabolic := by
    apply parabolic_pair_map_of_unipotent_and_marked_class hF hn _ (hUi s)
    obtain ⟨x,hx⟩ := hDm
    rcases hx with hp | hp
    · exact Or.inl (preserves_class_of_invariant D _ _ (hDi s) x hp)
    · exact Or.inr (preserves_class_of_invariant D _ _ (hDi s) x hp)
  refine ⟨e',?_⟩
  intro P hP
  have hPi (s : d.S) : P.map (α s).toMonoidHom = P := by
    rcases hP with rfl | hP
    · exact (hpair s).1
    · have he : P = planeParabolic := hP
      subst P
      exact (hpair s).2
  let B := (P.comap q).map K.subtype
  let R := d.normalizerParabolicResidual K (P.map e'.symm.toMonoidHom)
  have hR : R = (solvableResidual B).map B.subtype := by
    dsimp only [R]
    rw [d.normalizerParabolicResidual_eq_in_K]
    have he : (P.map e'.symm.toMonoidHom).comap (d.toNormalizerImage K) = P.comap q := by
      ext k
      change d.toNormalizerImage K k ∈ P.map e'.symm.toMonoidHom ↔ e' (d.toNormalizerImage K k) ∈ P
      constructor
      · rintro ⟨y,hy,he⟩
        rw [←he]
        change e' (e'.symm y) ∈ P
        rw [e'.apply_symm_apply]
        exact hy
      · intro hx
        exact ⟨_,hx,e'.symm_apply_apply _⟩
    rw [he,map_embedded_solvableResidual_of_hom]
  have hnB : d.S ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro x hx b hb
    obtain ⟨k,hk,rfl⟩ := hb
    let x₀ : d.S := ⟨x,hx⟩
    refine ⟨K.normalizerMonoidHom (inclusion hnK x₀) k,?_,rfl⟩
    change q (K.normalizerMonoidHom (inclusion hnK x₀) k) ∈ P
    rw [heq]
    exact hPi x₀ ▸ mem_map_of_mem (α x₀).toMonoidHom hk
  have hnR : d.S ≤ normalizer (R : Set G) := by
    rw [hR]
    exact hnB.trans (normalizer_le_normalizer_characteristic_image B (solvableResidual B))
  let : Group.IsPerfect R := hR ▸ Group.IsPerfect.map B.subtype
  obtain ⟨hfit,⟨er⟩⟩ := a.symplectic_four_residual_data hq hF hn e' P hP
  let : IsSimpleGroup SL(2,F) := NaturalExtension.model_simple (by omega)
  let : IsSimpleGroup (R ⧸ pCore 2 R) := er.isSimpleGroup
  let : Nontrivial R := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (pCore 2 R))
  have hz : center (R ⧸ pCore 2 R) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (R ⧸ pCore 2 R)) inferInstance with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hz)).elim
  let : IsQuasisimple (R ⧸ pCore 2 R) :=
    { simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hc : R.pCoreIn 2 ≠ ⊥ := by
    intro hh
    have hb : pCore 2 R = ⊥ := (map_eq_bot_iff_of_injective _ R.subtype_injective).mp hh
    have ht := centralizer_generalizedFitting_le R
    rw [hfit,hb] at ht
    rw [show centralizer ((⊥ : Subgroup R) : Set R) = ⊤ from
      centralizer_eq_top_iff_subset.mpr (show (⊥ : Subgroup R) ≤ center R from bot_le)] at ht
    have ht' : (⊤ : Subgroup R) = ⊥ := bot_unique ht
    exact (top_ne_bot : (⊤ : Subgroup R) ≠ ⊥) ht'
  exact ⟨(d.normalizerParabolicResidual_le K _).trans hK.1,
    (Chapter1.mem_LIn_of_normalized_perfect hK.2.2.1
      ((d.normalizerParabolicResidual_le K _).trans le_sup_left) hnR hc).2⟩



end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
