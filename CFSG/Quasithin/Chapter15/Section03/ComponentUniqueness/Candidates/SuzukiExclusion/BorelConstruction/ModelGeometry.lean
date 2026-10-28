module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.BorelConstruction.Invariance
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Orbit
public import Theory.GroupTheory.GeneralizedFitting.ComponentLocalClosure.Products
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.SpecificGroups.Suzuki.AbelianSubgroups
public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Marked geometry and characteristic two of the Suzuki orbit normalizer

For a centerless component whose normalizer has index at most two, its
S-orbit is a product of one or two actual conjugate components. Indexing by
distinct subgroups, as in `ComponentLocalClosure.Orbit`, gives independent
commuting factors and bounds their number by the normalizer index. The
subtype embedding identifies this product with the literal `localSpan L S`.

The orbit is normal in the component--Sylow join. Restricting the supplied
Sylow subgroup there and applying Sylow conjugacy in the product coordinates
carries its relative normalizer onto the product of the concrete Suzuki
Borels. This retains component permutation; L need not be S-invariant.

The root group is the two-core of a Suzuki Borel. Its centralizer is contained
in the root group, since this holds already for each nonidentity root element.
Self-centralizing two-cores pass to direct powers and across the marked
isomorphism, giving F*(B) = O₂(B) for the literal ambient candidate.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.34, printed pp.1134--1135; component calculus in 1.2.1(3)/A.3 and the
Suzuki Borel calculation in F.1.3(1). The root-element centralizer calculation
is Huppert--Blackburn III, XI.3.10 and XI.3.12(e).
-/

public section

open scoped Pointwise
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.BorelConstruction

private theorem bounded_orbit_power {G : Type*} [Group G] [Finite G]
    {L A : Subgroup G} (hL : IsComponent G L) (hZ : center L = ⊥)
    (hindex : (normalizer (L : Set G)).index ≤ 2) :
    ∃ n : ℕ, (n = 1 ∨ n = 2) ∧ Nonempty ((Fin n → L) ≃* componentOrbit L A) := by
  classical
  let O := {J : Subgroup G // ∃ a : A, L.map (MulAut.conj (a : G)).toMonoidHom = J}
  let a : O → A := fun i => Classical.choose i.property
  have ha (i : O) : L.map (MulAut.conj (a i : G)).toMonoidHom = i.val :=
    Classical.choose_spec i.property
  have hc : Pairwise fun i j : O => ∀ x y : G, x ∈ i.val → y ∈ j.val → Commute x y := by
    intro i j hij x y hx hy
    have hne : L.map (MulAut.conj (a i : G)).toMonoidHom ≠
        L.map (MulAut.conj (a j : G)).toMonoidHom := by
      rw [ha, ha]
      exact fun h => hij (Subtype.ext h)
    have hcomm := (hL.map_conj (a i)).commutator_eq_bot_of_ne (hL.map_conj (a j)) hne
    rw [ha, ha] at hcomm
    exact (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hx) y hy).symm
  have hz (i : O) : center i.val = ⊥ := by
    let e := ((MulAut.conj (a i : G)).subgroupMap L).trans (MulEquiv.subgroupCongr (ha i))
    apply bot_unique
    intro x hx
    have h : e.symm x ∈ center L := (centerCongr e.symm ⟨x, hx⟩).property
    rw [hZ, mem_bot] at h
    exact mem_bot.mpr (e.symm.injective (h.trans (map_one e.symm).symm))
  let : Fintype O := Fintype.ofFinite O
  let f : (∀ i : O, i.val) →* G := noncommPiCoprod hc
  have hf : Function.Injective f := injective_noncommPiCoprod_of_iSupIndep
    (iSupIndep_of_centerless_of_pairwise_commute (fun i : O => i.val) hz hc)
  have hr : f.range = componentOrbit L A := by
    rw [noncommPiCoprod_range]
    apply le_antisymm
    · refine iSup_le fun i => ?_
      rw [← ha i]
      exact le_iSup (fun a : A => L.map (MulAut.conj (a : G)).toMonoidHom) (a i)
    · refine iSup_le fun b => ?_
      exact le_iSup (fun i : O => i.val) ⟨_, b, rfl⟩
  let e₁ : (O → L) ≃* (∀ i : O, i.val) := MulEquiv.piCongrRight fun i =>
    ((MulAut.conj (a i : G)).subgroupMap L).trans (MulEquiv.subgroupCongr (ha i))
  let e₂ : (∀ i : O, i.val) ≃* componentOrbit L A :=
    (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  let : Nonempty O := ⟨⟨_, 1, rfl⟩⟩
  have hpos := Fintype.card_pos (α := O)
  have hcard : Fintype.card O ≤ 2 := by
    let X : Set (Subgroup G) := Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom
    have hX : X.ncard = (normalizer (L : Set G)).index := by
      let : MulAction G (Subgroup G) := MulAction.compHom (Subgroup G) MulAut.conj
      have he : normalizer (L : Set G) = MulAction.stabilizer G L := by
        ext g
        exact mem_normalizer_iff_map_conj_eq
      rw [he, MulAction.index_stabilizer]
      rfl
    have hle : Nat.card O ≤ Nat.card X := Nat.card_le_card_of_injective
      (fun i : O => (⟨i.val, ⟨a i, ha i⟩⟩ : X)) (by
        intro i j h
        exact Subtype.ext (congrArg (fun z : X => z.val) h))
    rw [Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hle
    exact hle.trans (hX ▸ hindex)
  refine ⟨Fintype.card O, by omega, ⟨?_⟩⟩
  exact (MulEquiv.arrowCongr (Fintype.equivFin O).symm (MulEquiv.refl L)).trans (e₁.trans e₂)

private def piSubgroupEquiv {J H : Type*} [Group H] (D : Subgroup H) :
    (pi Set.univ (fun _ : J => D)) ≃* (J → D) where
  toFun x i := ⟨x.val i, x.property i (Set.mem_univ i)⟩
  invFun x := ⟨fun i => (x i).val, fun i _ => (x i).property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private def powerSylow {J H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) : Sylow 2 (J → H) where
  toSubgroup := pi Set.univ (fun _ => (P : Subgroup H))
  isPGroup' := by
    have hp : IsPGroup 2 (J → P) := by
      obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_dvd_pow
      intro x
      refine ⟨n, funext fun i => ?_⟩
      exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard (x i)).trans hn)
    exact hp.of_injective (piSubgroupEquiv (J := J) (P : Subgroup H)).toMonoidHom
      (piSubgroupEquiv (J := J) (P : Subgroup H)).injective
  is_maximal' := by
    classical
    intro U hU hPU
    apply le_antisymm _ hPU
    intro x hx i _
    have he : U.map (Pi.evalMonoidHom (fun _ : J => H) i) = (P : Subgroup H) := by
      apply P.is_maximal' (hU.map _)
      intro y hy
      exact ⟨Pi.mulSingle i y, hPU ((mulSingle_mem_pi (H := fun _ : J => (P : Subgroup H)) i y).mpr (fun _ => hy)),
        by simp⟩
    exact he ▸ mem_map_of_mem (Pi.evalMonoidHom (fun _ : J => H) i) hx

private theorem normalizer_power {J H : Type*} [Group H] (D : Subgroup H) :
    normalizer (pi Set.univ (fun _ : J => D) : Set (J → H)) =
      pi Set.univ (fun _ : J => normalizer (D : Set H)) := by
  classical
  ext x
  constructor
  · intro hx i _
    change x i ∈ normalizer (D : Set H)
    rw [mem_normalizer_iff]
    intro y
    have he := mem_normalizer_iff.mp hx (Pi.mulSingle i y)
    have hfun : x * Pi.mulSingle i y * x⁻¹ = Pi.mulSingle i (x i * y * (x i)⁻¹) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp [Pi.mulSingle_eq_of_ne hj]
    simpa only [hfun, mulSingle_mem_pi, Set.mem_univ, true_implies] using he
  · intro hx
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy i _
      exact (mem_normalizer_iff.mp (hx i (Set.mem_univ i)) (y i)).mp (hy i (Set.mem_univ i))
    · intro hy i _
      exact (mem_normalizer_iff.mp (hx i (Set.mem_univ i)) (y i)).mpr (hy i (Set.mem_univ i))

private theorem marked_sylow_normalizer {H : Type*} [Group H] [Finite H]
    {n m : ℕ} (hm : 0 < m) (e : H ≃* (Fin n → SuzukiMatrixGroup m))
    (P : Sylow 2 H) :
    ∃ e' : H ≃* (Fin n → SuzukiMatrixGroup m),
      (normalizer (P : Set H)).map e'.toMonoidHom =
        pi Set.univ (fun _ => SuzukiBorelSubgroup m) := by
  obtain ⟨U, hU⟩ := suzukiRootSubgroup_isSylow m hm
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let R := powerSylow (J := Fin n) U
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Fin n → SuzukiMatrixGroup m) Q R
  let e' := e.trans (MulAut.conj g)
  have he : (P : Subgroup H).map e'.toMonoidHom =
      pi Set.univ (fun _ : Fin n => SuzukiRootSubgroup m) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((P : Subgroup H).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      pi Set.univ (fun _ : Fin n => (U : Subgroup (SuzukiMatrixGroup m))) at hh
    have he' : e'.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := by
      ext x
      rfl
    rw [he', ← map_map]
    simpa only [hU] using hh
  refine ⟨e', ?_⟩
  change (normalizer ((P : Subgroup H) : Set H)).map e'.toMonoidHom = _
  rw [map_normalizer_eq_of_bijective _ e'.bijective, he, normalizer_power,
    CFSG.Quasithin.ChapterF.Source.suzuki_root_normalizer_eq_borel]

private theorem orbit_map_subtype {G : Type*} [Group G]
    {I L S : Subgroup G} (hLI : L ≤ I) (hSI : S ≤ I) :
    (componentOrbit (L.subgroupOf I) (S.subgroupOf I)).map I.subtype = localSpan L S := by
  change (⨆ s : S.subgroupOf I,
    (L.subgroupOf I).map (MulAut.conj (s : I)).toMonoidHom).map I.subtype = _
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun s => ?_
    rintro x ⟨y, ⟨l, hl, rfl⟩, rfl⟩
    exact subset_closure ⟨(s : I).val, s.property, l.val, hl, rfl⟩
  · apply (closure_le _).mpr
    rintro x ⟨s, hs, l, hl, rfl⟩
    apply le_iSup (fun s : S.subgroupOf I =>
      ((L.subgroupOf I).map (MulAut.conj (s : I)).toMonoidHom).map I.subtype)
      ⟨⟨s, hSI hs⟩, hs⟩
    exact ⟨⟨s * l * s⁻¹, I.mul_mem (I.mul_mem (hSI hs) (hLI hl)) (I.inv_mem (hSI hs))⟩,
      ⟨⟨l, hLI hl⟩, hl, rfl⟩, rfl⟩

private theorem orbit_sylow {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) (P : Sylow 2 G) :
    ∃ Q : Sylow 2 (componentOrbit L (P : Subgroup G)),
      (Q : Subgroup _) = (P : Subgroup G).subgroupOf (componentOrbit L (P : Subgroup G)) := by
  let X := L ⊔ (P : Subgroup G)
  let D := componentOrbit L (P : Subgroup G)
  let N := D.subgroupOf X
  let : N.Normal := componentOrbit_normal_subgroupOf_sup L (P : Subgroup G)
  let T := P.subtype (show (P : Subgroup G) ≤ X from le_sup_right)
  obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal N
  let e : N ≃* D := subgroupOfEquivOfLe (componentOrbit_le_sup L (P : Subgroup G))
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (Q : Subgroup N).map e.toMonoidHom = _
  rw [hQ]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, componentOrbit_le_sup L (P : Subgroup G) x.property⟩, x.property⟩, hx, rfl⟩

/-- The concrete relative normalizer is a Borel in one or two actual Suzuki
factors. The isomorphism marks the whole subgroup, and S may permute the
components. No product marking or Borel-existence hypothesis is required. -/
theorem orbitNormalizer_model {G : Type*} [Group G] [Finite G]
    {I L S : Subgroup G} (hLI : L ≤ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I)) (m : ℕ) (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m)
    (hindex : (normalizer (L.subgroupOf I : Set I)).index ≤ 2) :
    ∃ n : ℕ, (n = 1 ∨ n = 2) ∧
      ∃ e₀ : localSpan L S ≃* (Fin n → SuzukiMatrixGroup m),
        ((orbitNormalizer L S).subgroupOf (localSpan L S)).map e₀.toMonoidHom =
          pi Set.univ (fun _ => SuzukiBorelSubgroup m) := by
  have hSI : S ≤ I := by
    rintro s hs
    rw [← hP] at hs
    obtain ⟨s, hs, rfl⟩ := hs
    exact s.property
  have hSP : S.subgroupOf I = (P : Subgroup I) := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hSI, hP]
  let eL : L.subgroupOf I ≃* SuzukiMatrixGroup m := (subgroupOfEquivOfLe hLI).trans e
  let : IsSimpleGroup (SuzukiMatrixGroup m) := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup (L.subgroupOf I) := eL.isSimpleGroup
  let : IsQuasisimple (L.subgroupOf I) := hL.2
  have hZ : center (L.subgroupOf I) = ⊥ := by
    rcases (inferInstance : (center (L.subgroupOf I)).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative (L.subgroupOf I) (center_eq_top_iff.mp hz)).elim
  let D := componentOrbit (L.subgroupOf I) (P : Subgroup I)
  obtain ⟨n, hn, ⟨f⟩⟩ := bounded_orbit_power (A := (P : Subgroup I)) hL hZ hindex
  have hD : D.map I.subtype = localSpan L S := by
    simpa only [hSP] using orbit_map_subtype hLI hSI
  let eD : D ≃* localSpan L S :=
    (D.equivMapOfInjective I.subtype I.subtype_injective).trans (MulEquiv.subgroupCongr hD)
  let e₀ : localSpan L S ≃* (Fin n → SuzukiMatrixGroup m) :=
    (eD.symm.trans f.symm).trans (MulEquiv.piCongrRight fun _ => eL)
  obtain ⟨Q, hQ⟩ := orbit_sylow (L.subgroupOf I) P
  let T := Q.mapSurjective (f := eD.toMonoidHom) eD.surjective
  have hT : (T : Subgroup (localSpan L S)) = S.subgroupOf (localSpan L S) := by
    change (Q : Subgroup D).map eD.toMonoidHom = _
    rw [hQ]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hP ▸ mem_map_of_mem I.subtype hy
    · intro hx
      refine ⟨eD.symm x, ?_, eD.apply_symm_apply x⟩
      change (eD.symm x : I) ∈ (P : Subgroup I)
      rw [← hSP]
      change ((eD.symm x : I) : G) ∈ S
      have heval : ((eD.symm x : I) : G) = (x : G) :=
        congrArg Subtype.val (eD.apply_symm_apply x)
      rwa [heval]
  obtain ⟨e', he'⟩ := marked_sylow_normalizer hm e₀ T
  refine ⟨n, hn, e', ?_⟩
  rw [orbitNormalizer_subgroupOf, ← hT]
  exact he'

/-- The constructed candidate satisfies the marked Suzuki-orbit predicate
used by the order-three automorphism detector. -/
theorem orbitNormalizer_isSuzukiOrbitBorel {G : Type*} [Group G] [Finite G]
    {I L S : Subgroup G} (hLI : L ≤ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I)) (m : ℕ) (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m)
    (hindex : (normalizer (L.subgroupOf I : Set I)).index ≤ 2) :
    IsSuzukiOrbitBorel ((orbitNormalizer L S).subgroupOf (localSpan L S)) := by
  obtain ⟨n, hn, e₀, he₀⟩ := orbitNormalizer_model hLI P hP hL m hm e hindex
  exact ⟨m, n, hm, hn, e₀, he₀⟩

private theorem borel_selfCentralizing (m : ℕ) (hm : 0 < m) :
    centralizer (pCore 2 (SuzukiBorelSubgroup m) : Set (SuzukiBorelSubgroup m)) ≤
      pCore 2 (SuzukiBorelSubgroup m) := by
  let B := SuzukiBorelSubgroup m
  have he : (pCore 2 B).map B.subtype = SuzukiRootSubgroup m := by
    obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
    have h := CFSG.Quasithin.ChapterF.Source.twoCore_sylow_normalizer P
    change (normalizer ((P : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))).pCoreIn 2 = _ at h
    rw [hP, suzukiRootSubgroup_normalizer m hm] at h
    exact h
  have : Nontrivial (SuzukiRootSubgroup m) := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [suzukiRootSubgroup_card m hm]
    have hq : 1 < 2 ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
    nlinarith
  obtain ⟨u, hu⟩ := exists_ne (1 : SuzukiRootSubgroup m)
  intro x hx
  have hc : (x : SuzukiMatrixGroup m) ∈ centralizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) := by
    rw [mem_centralizer_iff]
    intro y hy
    rw [← he] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact congrArg Subtype.val (mem_centralizer_iff.mp hx z hz)
  have hr : (x : SuzukiMatrixGroup m) ∈ SuzukiRootSubgroup m :=
    suzukiRootSubgroup_centralizer_le m hm u.property
      (fun h => hu (Subtype.ext h))
      ((centralizer_le (Set.singleton_subset_iff.mpr u.property)) hc)
  rw [← he] at hr
  obtain ⟨z, hz, hzx⟩ := hr
  exact (Subtype.ext hzx : z = x) ▸ hz

private theorem marked_borel_selfCentralizing {H : Type*} [Group H] [Finite H]
    {n m : ℕ} (hm : 0 < m) (B : Subgroup H)
    (e : H ≃* (Fin n → SuzukiMatrixGroup m))
    (he : B.map e.toMonoidHom = pi Set.univ (fun _ => SuzukiBorelSubgroup m)) :
    centralizer (pCore 2 B : Set B) ≤ pCore 2 B := by
  let eB : B ≃* (Fin n → SuzukiBorelSubgroup m) :=
    ((e.subgroupMap B).trans (MulEquiv.subgroupCongr he)).trans
      (piSubgroupEquiv (SuzukiBorelSubgroup m))
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 eB).mpr
    (centralizer_pCore_power_le (borel_selfCentralizing m hm))

/-- The constructed candidate has characteristic two in the source's
intrinsic generalized-Fitting convention. -/
theorem orbitNormalizer_generalizedFitting {G : Type*} [Group G] [Finite G]
    {I L S : Subgroup G} (hLI : L ≤ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I)) (m : ℕ) (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m)
    (hindex : (normalizer (L.subgroupOf I : Set I)).index ≤ 2) :
    generalizedFitting (orbitNormalizer L S) = pCore 2 (orbitNormalizer L S) := by
  obtain ⟨n, _, e₀, he₀⟩ := orbitNormalizer_model hLI P hP hL m hm e hindex
  have hc := marked_borel_selfCentralizing hm _ e₀ he₀
  apply generalizedFitting_eq_pCore_of_selfCentralizing
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (subgroupOfEquivOfLe (orbitNormalizer_le L S))).mp hc

end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.BorelConstruction
