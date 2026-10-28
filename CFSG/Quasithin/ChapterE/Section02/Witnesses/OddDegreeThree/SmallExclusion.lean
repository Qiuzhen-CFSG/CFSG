module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.OddDegreeThree.Original
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.ResidualCentralImage
public import Theory.ElementaryAbelian.Join
public import Theory.SpecificGroups.PSL3.OddInvolutionRoot
public import Theory.SpecificGroups.PSU3.OddInvolutionRoot
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Involution.SmallPrime
/-!
# Small automizers in the odd degree-three source rows

Residual centralization makes the original maximal Sylow overgroup normalize
V. Adjoining its central component involution to the image of V forces that
involution into the image, because every normal elementary subgroup has order
at most two. In the linear row it inverts an actual defining-characteristic
root. The original small-automizer theorem therefore forces p=3.

The exceptional PSL₃(3) local solvable-subgroup reduction is separate.
Source: Aschbacher–Smith E.2.17, printed p.230.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.Witnesses.OddDegreeThree
variable {H : Type*} [Group H] [Finite H]
private theorem central_involution_mem_of_normal_elementary_bound
    (M W : Subgroup H) [IsElementaryAbelian 2 W]
    (hWM : W ≤ M) (hMW : M ≤ normalizer (W : Set H)) (hW : W ≠ ⊥)
    (t : H) (ht : orderOf t = 2) (hM : M = centralizer ({t} : Set H))
    (hbound : ∀ A : Subgroup H, IsElementaryAbelian 2 A → A ≤ M →
      M ≤ normalizer (A : Set H) → Nat.card A ≤ 2) :
    t ∈ W ∧ Nat.card W = 2 := by
  let R := zpowers t
  have ht2 : t^2=1 := by simpa only [ht] using pow_orderOf_eq_one t
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.zpowers_of_pow_eq_one ht2
  have hRC : M ≤ centralizer (R : Set H) := by
    rw [hM]
    intro x hx y hy
    obtain ⟨n,rfl⟩ := hy
    exact (Commute.zpow_right (show Commute x t from mem_centralizer_singleton_iff.mp hx) n).eq.symm
  have hRM : R ≤ M := by
    rw [hM]
    exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hWR : R ≤ centralizer (W : Set H) :=
    le_centralizer_iff.mp (hWM.trans hRC)
  let A := W ⊔ R
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.sup_of_le_centralizer hWR
  have hMA : M ≤ normalizer (A : Set H) :=
    (le_inf hMW (hRC.trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup W R)
  have hAc : Nat.card A ≤ 2 := hbound A inferInstance (sup_le hWM hRM) hMA
  have hWc : 2 ≤ Nat.card W := by have := (one_lt_card_iff_ne_bot W).mpr hW; omega
  have he : W = A := eq_of_le_of_card_ge le_sup_left (hAc.trans hWc)
  exact ⟨he ▸ (show t ∈ A from (show R ≤ A from le_sup_right) (mem_zpowers t)),
    le_antisymm ((card_le_of_le (show W ≤ A from le_sup_left)).trans hAc) hWc⟩

/-- The actual nontrivial image contains the central component involution. -/
theorem linear_source_image_involution
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
    Nat.card (V.map q) = 2 ∧ ∃ t : K.map q, orderOf t = 2 ∧
      (t : H ⧸ ChapterB.minimalParabolicCore T hP) ∈ V.map q := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let D := K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : D.Normal := hi.2.2.1
  let : IsSimpleGroup D := hi.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hO : pCore 2 (H ⧸ J) = ⊥ := bot_unique
    ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans
      (Structure.source_star_minimal_core_free T hP).2.le)
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWM : W ≤ ChapterB.minimalParabolicMax S hmin :=
    (map_mono hVT).trans (ChapterB.minimalParabolicMax_spec S hmin).2
  have hMW : ChapterB.minimalParabolicMax S hmin ≤ normalizer (W : Set (H ⧸ J)) := by
    rw [hmax]
    exact (map_mono (source_maximal_normalizes_of_residual_centralizes T hP V hVT hvn hres)).trans
      (le_normalizer_map q)
  have hne : W ≠ ⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q, QuotientGroup.ker_mk'] using hle)
  obtain ⟨t,ht,_,_,hM,_⟩ := Structure.OddDegreeThree.linear_involution_centralizer
    S hmin D hi.2.2.2 hO hp ho hm
  have hbound := Structure.OddDegreeThree.linear_normal_elementary_card_le_two
    S hmin D hi.2.2.2 hO hp ho hm
  obtain ⟨htW,hcard⟩ := central_involution_mem_of_normal_elementary_bound
    (ChapterB.minimalParabolicMax S hmin) W hWM hMW hne t
    (by simpa using ht) hM (fun A hA hAM hMA => @hbound A hA hAM hMA)
  exact ⟨hcard,t,ht,htW⟩
/-- The actual nontrivial image contains the central component involution. -/
theorem unitary_source_image_involution
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
    p%4=1 ∧ Nat.card (V.map q) = 2 ∧ ∃ t : K.map q, orderOf t = 2 ∧
      (t : H ⧸ ChapterB.minimalParabolicCore T hP) ∈ V.map q := by
  let J := ChapterB.minimalParabolicCore T hP
  let M := ChapterB.minimalParabolicMax T hP
  let q := QuotientGroup.mk' J
  let S := T.mapSurjective (QuotientGroup.mk'_surjective J)
  let W := V.map q
  let D := K.map q
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
  have hi := Structure.source_normal_simple_image T hP hs K hK hgen
  let : D.Normal := hi.2.2.1
  let : IsSimpleGroup D := hi.1
  have hmin := (Structure.source_star_minimal_core_free T hP).1
  have hO : pCore 2 (H ⧸ J) = ⊥ := bot_unique
    ((ChapterB.minimalParabolicTwoCore_le_core S hmin).trans
      (Structure.source_star_minimal_core_free T hP).2.le)
  have hmax : ChapterB.minimalParabolicMax S hmin = M.map q :=
    (ChapterB.minimalParabolicMax_map_core T hP q (QuotientGroup.mk'_surjective J)
      (by rw [QuotientGroup.ker_mk'])).symm
  have hWM : W ≤ ChapterB.minimalParabolicMax S hmin :=
    (map_mono hVT).trans (ChapterB.minimalParabolicMax_spec S hmin).2
  have hMW : ChapterB.minimalParabolicMax S hmin ≤ normalizer (W : Set (H ⧸ J)) := by
    rw [hmax]
    exact (map_mono (source_maximal_normalizes_of_residual_centralizes T hP V hVT hvn hres)).trans
      (le_normalizer_map q)
  have hne : W ≠ ⊥ := by
    intro hh
    have hle := (map_eq_bot_iff V).mp hh
    exact hout (by simpa only [q, QuotientGroup.ker_mk'] using hle)
  obtain ⟨hmod,t,ht,_,_,hM,_⟩ := Structure.OddDegreeThree.unitary_centralizer_congruence
    S hmin D hi.2.2.2 hp ho hm
  have hbound (A : Subgroup (H ⧸ J)) [IsElementaryAbelian 2 A]
      (hAM : A ≤ ChapterB.minimalParabolicMax S hmin)
      (hMA : ChapterB.minimalParabolicMax S hmin ≤ normalizer (A : Set (H ⧸ J))) :
      Nat.card A ≤ 2 := by
    apply Structure.OddDegreeThree.unitary_elementary_card_le_two
      S hmin D hi.2.2.2 hO hp ho hm A
    exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 A) hAM hMA
  obtain ⟨htW,hcard⟩ := central_involution_mem_of_normal_elementary_bound
    (ChapterB.minimalParabolicMax S hmin) W hWM hMW hne t
    (by simpa using ht) hM (fun A hA hAM hMA => @hbound A hA hAM hMA)
  exact ⟨hmod,hcard,t,ht,htW⟩

variable {D : Type*} [Group D] [Finite D]

/-- The original linear model parameter is three under the small automizer hypotheses. -/
theorem linear_source_prime_eq_three
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio
      (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    p = 3 := by
  obtain ⟨hcard,t,ht,htV⟩ := linear_source_image_involution
    T hP hs K hK hgen hp ho hm V hVT hvn hout hres
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨r,hr,htr⟩ := Matrix.PSL3.OddInvolutionRoot.exists_inverted_root hp ho hF
    (e t) ((e.orderOf_eq t).trans ht)
  let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
  let j := (K.map q).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  have hjt : j (e t) = (t : H ⧸ ChapterB.minimalParabolicCore T hP) := by
    change (e.symm (e t)).val = t.val
    rw [e.symm_apply_apply]
  have htne : (t : H ⧸ ChapterB.minimalParabolicCore T hP) ≠ 1 := by
    intro hh
    have h1 : t=1 := Subtype.ext hh
    simp [h1] at ht
  have hp2 : p≠2 := by intro h; rw [h] at ho; norm_num at ho
  apply Involution.source_prime_inverter_eq_three T hP V hVT hvn hcore hout hfit hV
    U hTU hU f hf hk hD hratio hcard hp hp2 t (j r) htV htne
      ((orderOf_injective j hj r).trans hr)
  simpa only [map_mul,map_inv,hjt] using congrArg j htr

/-- The original unitary degree-three source row is impossible with a small automizer. -/
theorem unitary_source_small_false
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSU
      (K.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) 3 p)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬V ≤ ChapterB.minimalParabolicCore T hP)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (U : Subgroup H) (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio
      (DihedralCubic.representation U V hU f hf hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax T hP)).map
      (ChapterB.minimalParabolicMax T hP).subtype ≤ centralizer (V : Set H)) :
    False := by
  obtain ⟨hmod,hcard,t,ht,htV⟩ := unitary_source_image_involution
    T hP hs K hK hgen hp ho hm V hVT hvn hout hres
  have hp2 : p≠2 := by intro h; rw [h] at ho; norm_num at ho
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
  obtain ⟨r,hr,htr⟩ := BenderSuzuki.MatrixGroups.HermitianForm.OddInvolutionRoot.exists_inverted_root J hp hp2 hF hc
    (e t) ((e.orderOf_eq t).trans ht)
  let q := QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)
  let j := (K.map q).subtype.comp e.symm.toMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp e.symm.injective
  have hjt : j (e t) = (t : H ⧸ ChapterB.minimalParabolicCore T hP) := by
    change (e.symm (e t)).val = t.val
    rw [e.symm_apply_apply]
  have htne : (t : H ⧸ ChapterB.minimalParabolicCore T hP) ≠ 1 := by
    intro hh
    have h1 : t=1 := Subtype.ext hh
    simp [h1] at ht
  have hp3 : p=3 := by
    apply Involution.source_prime_inverter_eq_three T hP V hVT hvn hcore hout hfit hV
      U hTU hU f hf hk hD hratio hcard hp hp2 t (j r) htV htne
        ((orderOf_injective j hj r).trans hr)
    simpa only [map_mul,map_inv,hjt] using congrArg j htr
  omega


end CFSG.Quasithin.ChapterE.Witnesses.OddDegreeThree
