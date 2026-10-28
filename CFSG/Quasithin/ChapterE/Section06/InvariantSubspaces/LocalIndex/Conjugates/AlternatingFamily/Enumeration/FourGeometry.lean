module
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Lifts
public import Theory.GroupTheory.ElementaryThompsonFourFamily

/-!
# Four-family geometry from the marked alternating-five action

The elementary kernel and its full-image opposite cover every elementary
subgroup by four maximum members. The actual fixed-space profile determines
the common intersection and adjacent indices. Binary coordinates separate the
crossing commutators: one fixes the third coordinate, while the other changes
it. These give the geometry for the four-family Thompson count.

Source: Aschbacher–Smith C.6.1, printed p.165, using the C.5.6 marked action
and the elementary-lift argument of B.2.21.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
variable {T : Type*} [Group T] [Finite T]

omit [Finite T] in
private theorem fixed_eq_of_image_eq (σ : T →* Perm) (V A B : Subgroup T)
    [IsElementaryAbelian 2 V] (hk : σ.ker = V) (he : A.map σ = B.map σ) :
    V ⊓ centralizer (A : Set T) = V ⊓ centralizer (B : Set T) := by
  have hle (A B : Subgroup T) (he : A.map σ = B.map σ) :
      V ⊓ centralizer (A : Set T) ≤ V ⊓ centralizer (B : Set T) := by
    rintro v ⟨hv,hc⟩
    refine ⟨hv,?_⟩
    intro b hb
    have hsb : σ b ∈ A.map σ := he ▸ mem_map_of_mem σ hb
    obtain ⟨a,ha,hab⟩ := hsb
    have hd : a⁻¹*b ∈ V := by rw [←hk,MonoidHom.mem_ker]; simp [hab]
    have h1 : Commute a v := hc a ha
    have h2 : Commute (a⁻¹*b) v := setLike_mul_comm hd hv
    simpa using (h1.mul_left h2).eq
  exact le_antisymm (hle A B he) (hle B A he.symm)

omit [Finite T] in
private theorem fixed_singleton_of_line (σ : T →* Perm) (V A : Subgroup T)
    [IsElementaryAbelian 2 V] (hk : σ.ker = V) (i : Fin 2)
    (hi : A.map σ = line i) (a : T) (hai : σ a = transposition i) :
    V ⊓ centralizer (A : Set T) = V ⊓ centralizer ({a} : Set T) := by
  have he : A.map σ = (zpowers a).map σ := by rw [MonoidHom.map_zpowers,hai]; exact hi
  rw [fixed_eq_of_image_eq σ V A (zpowers a) hk he,zpowers_eq_closure,centralizer_closure]

omit [Finite T] in
/-- An elementary lift of a cyclic actor lies in the fixed-saturated lift. -/
private theorem cyclic_lift_le (σ : T →* Perm) (V A B : Subgroup T)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hk : σ.ker = V) (he : A.map σ = B.map σ)
    (hfa : V ⊓ centralizer (A : Set T) ≤ A)
    (a : T) (ha : a ∈ A)
    (hfix : V ⊓ centralizer (A : Set T) = V ⊓ centralizer ({a} : Set T)) : B ≤ A := by
  let F := V ⊓ centralizer (B : Set T)
  let C := B ⊔ F
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hFmap : F.map σ = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (inf_le_left.trans hk.ge)
  have hCmap : C.map σ = B.map σ := by rw [Subgroup.map_sup,hFmap,sup_bot_eq]
  have hfc : V ⊓ centralizer (C : Set T) ≤ C := by
    intro z hz
    apply (show F ≤ C from le_sup_right)
    exact ⟨hz.1, fun b hb => hz.2 b (show b ∈ C from (show B ≤ C from le_sup_left) hb)⟩
  have hCA := IsElementaryAbelian.le_of_same_image_of_centralizer_singleton
    σ V A C hk hfa hfc (he.trans hCmap.symm) a ha hfix
  exact le_sup_left.trans hCA

private theorem max_fixed_le (V A : Subgroup T) [IsElementaryAbelian 2 V]
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T)) :
    V ⊓ centralizer (A : Set T) ≤ A := by
  let : IsElementaryAbelian 2 (V ⊓ centralizer (A : Set T) : Subgroup T) :=
    IsElementaryAbelian.of_le inf_le_left
  exact Stellmacher.maxElementary_contains_elementary_centralizer ⊤ A _ hA le_top inf_le_right

/-- Every elementary subgroup lies in one of the four maximum members. -/
theorem marked_elementary_cover (σ : T →* Perm) (V W P P' : Subgroup T)
    [IsElementaryAbelian 2 V]
    (hk : σ.ker = V) (hr : σ.range = ChapterB.Offenders.D 5)
    (hp : FixedProfile σ V)
    (hW : W ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hP : P ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hP' : P' ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hWmap : W.map σ = ChapterB.Offenders.D 5)
    (hPmap : P.map σ = line 0) (hP'map : P'.map σ = line 1)
    (B : Subgroup T) (hB : IsElementaryAbelian 2 B) :
    B ≤ V ∨ B ≤ W ∨ B ≤ P ∨ B ≤ P' := by
  let : IsElementaryAbelian 2 B := hB
  let : IsElementaryAbelian 2 W := hW.2.1
  let : IsElementaryAbelian 2 P := hP.2.1
  let : IsElementaryAbelian 2 P' := hP'.2.1
  have hl (A : Subgroup T) [IsElementaryAbelian 2 A]
      (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
      (i : Fin 2) (hAi : A.map σ = line i) (hBi : B.map σ = line i) : B ≤ A := by
    obtain ⟨a,ha,hai⟩ := (show transposition i ∈ A.map σ from hAi ▸ mem_zpowers _)
    exact cyclic_lift_le σ V A B hk (hAi.trans hBi.symm) (max_fixed_le V A hA) a ha
      (fixed_singleton_of_line σ V A hk i hAi a hai)
  rcases subgroup_cases (B.map σ) ((B.map_le_range σ).trans hr.le) with hb | hb | hb | hb | hb
  · exact Or.inl ((Subgroup.map_eq_bot_iff B).mp hb |>.trans hk.le)
  · exact Or.inr (Or.inr (Or.inl (hl P hP 0 hPmap hb)))
  · exact Or.inr (Or.inr (Or.inr (hl P' hP' 1 hP'map hb)))
  · obtain ⟨w,hw,hwi⟩ := (show doubleSwap ∈ W.map σ from
      hWmap ▸ (mem_actor _).mpr (Or.inr (Or.inr (Or.inr rfl))))
    let A := W ⊓ diagonal.comap σ
    have hA : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
    let := hA
    have haw : w ∈ A := ⟨hw,by change σ w ∈ diagonal; rw [hwi]; exact mem_zpowers _⟩
    have hAm : A.map σ = diagonal := by
      apply le_antisymm
      · rintro p ⟨a,ha,rfl⟩; exact ha.2
      · apply zpowers_le.mpr
        exact hwi ▸ mem_map_of_mem σ haw
    have hfixed : V ⊓ centralizer (A : Set T) = V ⊓ centralizer (W : Set T) := by
      have h1 := hp.card_fixed A
      have h2 := hp.card_fixed W
      rw [hAm,fixedIndex_diagonal] at h1
      rw [hWmap,fixedIndex_actor] at h2
      symm
      apply eq_of_le_of_card_ge _ (by omega)
      exact inf_le_inf_left V (centralizer_le (show A ≤ W from inf_le_left))
    have hfa : V ⊓ centralizer (A : Set T) ≤ A := by
      rw [hfixed]
      exact le_inf (max_fixed_le V W hW) (by
        intro z hz
        change σ z ∈ diagonal
        have hz1 : σ z = 1 := by change z ∈ σ.ker; rw [hk]; exact hz.1
        rw [hz1]; exact one_mem _)
    have hdet : V ⊓ centralizer (A : Set T) = V ⊓ centralizer ({w} : Set T) :=
      hfixed.trans (hp.full_detect W w hw hWmap hwi)
    exact Or.inr (Or.inl ((cyclic_lift_le σ V A B hk (hAm.trans hb.symm) hfa w haw hdet).trans inf_le_left))
  · obtain ⟨w,hw,hwi⟩ := (show doubleSwap ∈ W.map σ from
      hWmap ▸ (mem_actor _).mpr (Or.inr (Or.inr (Or.inr rfl))))
    exact Or.inr (Or.inl (cyclic_lift_le σ V W B hk (hWmap.trans hb.symm)
      (max_fixed_le V W hW) w hw (hp.full_detect W w hw hWmap hwi)))

private theorem max_inf_kernel (V A : Subgroup T) [IsElementaryAbelian 2 V]
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T)) :
    V ⊓ A = V ⊓ centralizer (A : Set T) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  exact le_antisymm (inf_le_inf_left V (le_centralizer A))
    (le_inf inf_le_left (max_fixed_le V A hA))

/-- The common intersection is the full-actor fixed subgroup of the core. -/
theorem marked_intersections (σ : T →* Perm) (V W P P' : Subgroup T)
    [IsElementaryAbelian 2 V] (hk : σ.ker = V) (hp : FixedProfile σ V)
    (hW : W ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hP : P ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hP' : P' ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hWmap : W.map σ = ChapterB.Offenders.D 5)
    (hPmap : P.map σ = line 0) (hP'map : P'.map σ = line 1) :
    P ⊓ P' = V ⊓ W ∧
      V.relIndex P = 2 ∧ V.relIndex P' = 2 ∧
      4 * Nat.card (V ⊓ W : Subgroup T) = Nat.card V := by
  let : IsElementaryAbelian 2 W := hW.2.1
  let : IsElementaryAbelian 2 P := hP.2.1
  let : IsElementaryAbelian 2 P' := hP'.2.1
  have hjoin : (P ⊔ P').map σ = W.map σ := by
    rw [Subgroup.map_sup,hPmap,hP'map,hWmap,actor_eq_sup]
  have hfixed := fixed_eq_of_image_eq σ V (P ⊔ P') W hk hjoin
  have he : P ⊓ P' = V ⊓ W := by
    rw [max_inf_kernel V W hW,←hfixed]
    apply le_antisymm
    · rintro z ⟨hz,hz'⟩
      have hzV : z ∈ V := by
        rw [←hk,MonoidHom.mem_ker]
        have h0 : σ z = 1 ∨ σ z = transposition 0 :=
          (mem_line 0 _).mp (hPmap ▸ mem_map_of_mem σ hz)
        have h1 : σ z = 1 ∨ σ z = transposition 1 :=
          (mem_line 1 _).mp (hP'map ▸ mem_map_of_mem σ hz')
        rcases h0 with h0 | h0
        · exact h0
        rcases h1 with h1 | h1
        · exact h1
        have hne : transposition 0 ≠ transposition 1 := by decide +kernel
        exact (hne (h0.symm.trans h1)).elim
      refine ⟨hzV,?_⟩
      have hc : P ⊔ P' ≤ centralizer ({z} : Set T) := by
        apply sup_le
        · intro p hp
          exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hp hz)
        · intro p hp
          exact mem_centralizer_singleton_iff.mpr (setLike_mul_comm hp hz')
      exact fun a ha => mem_centralizer_singleton_iff.mp (hc ha)
    · intro z hz
      exact ⟨max_fixed_le V P hP ⟨hz.1, fun p hp => hz.2 p ((show P ≤ P ⊔ P' from le_sup_left) hp)⟩,
        max_fixed_le V P' hP' ⟨hz.1, fun p hp => hz.2 p ((show P' ≤ P ⊔ P' from le_sup_right) hp)⟩⟩
  refine ⟨he,?_,?_,?_⟩
  · rw [←hk,relIndex_ker,hPmap,line_card]
  · rw [←hk,relIndex_ker,hP'map,line_card]
  · rw [max_inf_kernel V W hW]
    have hh := hp.card_fixed W
    rw [hWmap,fixedIndex_actor] at hh
    omega

open scoped commutatorElement Pointwise
open BinaryPermutation

private def coordinateTwo : Multiplicative Vector →* Multiplicative (ZMod 2) where
  toFun v := Multiplicative.ofAdd (v.toAdd.val 2)
  map_one' := rfl
  map_mul' _ _ := rfl

private def seed : Vector := ⟨![0,0,1,0,1],by change ∑ i : Fin 5, ![0,0,1,0,1] i = (0 : ZMod 2); decide +kernel⟩

omit [Finite T] in
private theorem lift_commutator (σ : T →* Perm) (ι : Multiplicative Vector →* T)
    (he : ∀ (s : T) (v : Vector), ι (Multiplicative.ofAdd (coreRepresentation (Fin 5) (σ s) v)) =
      s * ι (Multiplicative.ofAdd v) * s⁻¹) (u : Vector) (s : T) :
    ⁅ι (Multiplicative.ofAdd u),s⁆ =
      ι (Multiplicative.ofAdd (u - coreRepresentation (Fin 5) (σ s) u)) := by
  have hh : Multiplicative.ofAdd (u - coreRepresentation (Fin 5) (σ s) u) =
      Multiplicative.ofAdd u * (Multiplicative.ofAdd (coreRepresentation (Fin 5) (σ s) u))⁻¹ := by
    rw [sub_eq_add_neg,ofAdd_add,ofAdd_neg]
  rw [hh,map_mul,map_inv,he]
  simp only [commutatorElement_def,mul_inv_rev,inv_inv]
  group

/-- The two crossing commutators are different in the actual marked module. -/
theorem marked_cross_ne (σ : T →* Perm) (V W P P' D : Subgroup T)
    [IsElementaryAbelian 2 V]
    (hk : σ.ker = V)
    (hW : W ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hP : P ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hP' : P' ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hWmap : W.map σ = ChapterB.Offenders.D 5)
    (hPmap : P.map σ = line 0) (hP'map : P'.map σ = line 1)
    (ι : Multiplicative Vector →* T) (hi : Function.Injective ι)
    (hprod : V = ι.range ⊔ D) (hD : D ≤ center T)
    (he : ∀ (s : T) (v : Vector), ι (Multiplicative.ofAdd (coreRepresentation (Fin 5) (σ s) v)) =
      s * ι (Multiplicative.ofAdd v) * s⁻¹) :
    ⁅V ⊓ P,W ⊓ P'⁆ ≠ ⁅V ⊓ P',W ⊓ P⁆ := by
  let : IsElementaryAbelian 2 W := hW.2.1
  let : IsElementaryAbelian 2 P := hP.2.1
  let : IsElementaryAbelian 2 P' := hP'.2.1
  let Z := coordinateTwo.ker.map ι
  have hUr : ι.range ≤ V := hprod ▸ le_sup_left
  have hDZ : D ≤ centralizer (ι.range : Set T) := hD.trans (center_le_centralizer _)
  have hbound : ⁅V,P⁆ ≤ Z := by
    apply commutator_le.mpr
    intro q hq p hp
    have hqprod : q ∈ (ι.range : Set T) * (D : Set T) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (hDZ.trans (Subgroup.centralizer_le_normalizer _)),←hprod]
      exact hq
    obtain ⟨_,⟨u,rfl⟩,d,hd,rfl⟩ := hqprod
    have hdp : ⁅d,p⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      ((mem_center_iff.mp (hD hd) p).symm)
    rw [commutatorElement_mul_left_eq_conj_mul,hdp,mul_one,mul_inv_cancel,one_mul]
    have hh := lift_commutator σ ι he u.toAdd p
    simp only [ofAdd_toAdd] at hh
    rw [hh]
    apply mem_map_of_mem
    change (u.toAdd - coreRepresentation (Fin 5) (σ p) u.toAdd).val 2 = 0
    have hpi : σ p ∈ line 0 := hPmap ▸ mem_map_of_mem σ hp
    rcases (mem_line 0 _).mp hpi with hpi | hpi
    · rw [hpi]; simp
    · rw [hpi]
      change u.toAdd.val 2 - u.toAdd.val ((transposition 0).symm 2) = 0
      have hf : (transposition 0).symm 2 = 2 := by decide +kernel
      rw [hf,sub_self]
  obtain ⟨w,hw,hwi⟩ := (show transposition 1 ∈ W.map σ from
    hWmap ▸ ChapterB.Offenders.pairSwap_mem (n := 5) 1 (by decide))
  let B := W ⊓ (line 1).comap σ
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le inf_le_left
  have hwB : w ∈ B := ⟨hw,by change σ w ∈ line 1; rw [hwi]; exact mem_zpowers _⟩
  have hBm : B.map σ = line 1 := by
    apply le_antisymm
    · rintro p ⟨b,hb,rfl⟩; exact hb.2
    · exact zpowers_le.mpr (hwi ▸ mem_map_of_mem σ hwB)
  obtain ⟨p,hp,hpi⟩ := (show transposition 1 ∈ P'.map σ from hP'map ▸ mem_zpowers _)
  have hBP : B ≤ P' := cyclic_lift_le σ V P' B hk (hP'map.trans hBm.symm)
    (max_fixed_le V P' hP') p hp (fixed_singleton_of_line σ V P' hk 1 hP'map p hpi)
  have hwP' : w ∈ W ⊓ P' := ⟨hw,hBP hwB⟩
  have huV : ι (Multiplicative.ofAdd seed) ∈ V := hUr ⟨_,rfl⟩
  have huP : ι (Multiplicative.ofAdd seed) ∈ P := by
    apply max_fixed_le V P hP
    refine ⟨huV,?_⟩
    intro p hp
    have hpi : σ p ∈ line 0 := hPmap ▸ mem_map_of_mem σ hp
    have hfix : coreRepresentation (Fin 5) (σ p) seed = seed := by
      rcases (mem_line 0 _).mp hpi with hpi | hpi
      · rw [hpi]; rfl
      · rw [hpi]; decide +kernel
    have hh := he p seed
    rw [hfix] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hz : ⁅ι (Multiplicative.ofAdd seed),w⁆ ∈ ⁅V ⊓ P,W ⊓ P'⁆ :=
    commutator_mem_commutator ⟨huV,huP⟩ hwP'
  intro hcross
  rw [hcross] at hz
  have hzZ := hbound (commutator_mono inf_le_left inf_le_right hz)
  rw [lift_commutator σ ι he seed w,hwi] at hzZ
  obtain ⟨v,hv,hvι⟩ := hzZ
  have hvδ := hi hvι
  rw [hvδ] at hv
  have hnot : Multiplicative.ofAdd (seed - coreRepresentation (Fin 5) (transposition 1) seed) ∉
      coordinateTwo.ker := by decide +kernel
  exact hnot hv

/-- The literal permutation module supplies all eight geometric inputs for
four-family Thompson stability. -/
theorem marked_four_geometry (σ : T →* Perm) (V W P P' D : Subgroup T)
    [IsElementaryAbelian 2 V]
    (hk : σ.ker = V) (hr : σ.range = ChapterB.Offenders.D 5)
    (hp : FixedProfile σ V)
    (hW : W ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hP : P ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hP' : P' ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hWmap : W.map σ = ChapterB.Offenders.D 5)
    (hPmap : P.map σ = line 0) (hP'map : P'.map σ = line 1)
    (hVW : V ≤ normalizer (W : Set T)) (hWV : W ≤ normalizer (V : Set T))
    (ι : Multiplicative Vector →* T) (hi : Function.Injective ι)
    (hprod : V = ι.range ⊔ D) (hD : D ≤ center T)
    (he : ∀ (s : T) (v : Vector), ι (Multiplicative.ofAdd (coreRepresentation (Fin 5) (σ s) v)) =
      s * ι (Multiplicative.ofAdd v) * s⁻¹) :
    Stellmacher.FourFamilyGeometry (⊤ : Subgroup T) V W P P' (V ⊓ W) := by
  obtain ⟨hopp,hiP,hiP',hcard⟩ := marked_intersections σ V W P P' hk hp hW hP hP'
    hWmap hPmap hP'map
  refine ⟨?_,rfl,hopp,hiP.le,hiP'.le,hcard.le,?_,?_⟩
  · intro B _ hB
    exact marked_elementary_cover σ V W P P' hk hr hp hW hP hP' hWmap hPmap hP'map B hB
  · exact (commutator_mono inf_le_left inf_le_left).trans
      (le_inf (le_normalizer_iff_commutator_le_left.mp hWV)
        (le_normalizer_iff_commutator_le_right.mp hVW))
  · exact marked_cross_ne σ V W P P' D hk hW hP hP' hWmap hPmap hP'map ι hi hprod hD he
end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
