module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.TerminalRudvalis.Geometry
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.TerminalRudvalis.Action

/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.TerminalRudvalis.Geometry`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]


private theorem native_sizes (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (j : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map j.toMonoidHom
    let C := normalizer (E : Set Rudvalis.Model)
    Nat.card C = 64 * 12096 ∧ ∀ z : E, z ≠ 1 →
      Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C) = 12288 := by
  obtain ⟨a,d,ha,hk,hd,he,hN,hpoint⟩ := unitary_terminal_native_full_action s A hAN hcomm hodd hAV J j hV hR
  exact ⟨hN,hpoint⟩

private theorem native_points (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (j : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map j.toMonoidHom
    ∀ z : E, z ≠ 1 → IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) := by
  obtain ⟨hel,hE,hB,hcore,hEB,hBE,ht,hcent⟩ := unitary_terminal_native_centralizer s A hAN hcomm hodd hAV J j hV hR
  let E := (V.subgroupOf J).map j.toMonoidHom
  let B := ((oddActorResidual L A).subgroupOf J).map j.toMonoidHom
  let : IsElementaryAbelian 2 E := hel
  dsimp only
  intro z hz
  exact (Rudvalis.transitive_sixtyFour_involution_class B E hBE hE
    (by rw [hB]; exact dvd_mul_left _ _) ht z hz).1

/-- The original module meets the ambient point two-core in order 32. -/
theorem unitary_terminal_native_module_core_intersection (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (mark : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map mark.toMonoidHom
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      Nat.card (E ⊓ D.pCoreIn 2 : Subgroup Rudvalis.Model) = 32 := by
  let E := (V.subgroupOf J).map mark.toMonoidHom
  let C := normalizer (E : Set Rudvalis.Model)
  obtain ⟨a,d,ha,hker,_,he,hCcard,hpoint⟩ :=
    unitary_terminal_native_full_action s A hAN hcomm hodd hAV J mark hV hR
  have hCE : C ≤ normalizer (E : Set Rudvalis.Model) := le_rfl
  let hEelem : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective d.symm.toMonoidHom d.symm.surjective
  let : IsMulCommutative E := hEelem.toIsMulCommutative
  let : Module (ZMod 2) (Additive E) := IsElementaryAbelian.isVectorSpace 2
  let ed : Additive E ≃ₗ[ZMod 2] Additive V :=
    { d.toAdditive with map_smul' := ZMod.map_smul d.toAdditive }
  let θ := ed.trans s.coordinates
  let α : C →* MulAut E := E.normalizerMonoidHom.comp (inclusion hCE)
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  let P := D.subgroupOf C
  have hED : E ≤ D := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact setLike_mul_comm hu z.property
  let j : E →* D := inclusion hED
  obtain ⟨q,_,hqk,_,_,_⟩ :=
    Rudvalis.point_core_intersection_quotient C z (native_points s A hAN hcomm hodd hAV J mark hV hR z hz)
      ((native_sizes s A hAN hcomm hodd hAV J mark hV hR).2 z hz)
  let k := q.comp j
  have hk : k.ker = (D.pCoreIn 2).subgroupOf E := by
    ext u
    change q (j u) = 1 ↔ (u : Rudvalis.Model) ∈ D.pCoreIn 2
    change j u ∈ q.ker ↔ _
    rw [hqk]
    constructor
    · intro hu
      exact ⟨j u,hu,rfl⟩
    · rintro ⟨v,hv,heq⟩
      exact (show v = j u from Subtype.ext heq) ▸ hv
  have hmap : k.ker.map E.subtype = E ⊓ D.pCoreIn 2 := by
    rw [hk,subgroupOf_map_subtype,inf_comm]
  have hv : θ (Additive.ofMul z) ≠ 0 := by
    intro hh
    apply hz
    apply Additive.ofMul.injective
    apply θ.injective
    change θ (Additive.ofMul z) = θ 0
    rw [map_zero]
    exact hh
  have hP (x : C) : x ∈ P ↔ Atlas.G2.Natural.action (ZMod 2) (a x)
      (θ (Additive.ofMul z)) = θ (Additive.ofMul z) := by
    change x ∈ P ↔ Atlas.G2.Natural.action (ZMod 2) (a x)
      (s.coordinates (Additive.ofMul (d z))) = s.coordinates (Additive.ofMul (d z))
    rw [←he x z,s.coordinates.injective.eq_iff,Additive.ofMul.injective.eq_iff,d.injective.eq_iff]
    change (x : Rudvalis.Model) ∈ centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model) ↔ _
    rw [mem_centralizer_singleton_iff]
    rw [Subtype.ext_iff]
    change (x : Rudvalis.Model)*(z : Rudvalis.Model) = (z : Rudvalis.Model)*(x : Rudvalis.Model) ↔
      (x : Rudvalis.Model)*(z : Rudvalis.Model)*(x : Rudvalis.Model)⁻¹ = (z : Rudvalis.Model)
    rw [mul_inv_eq_iff_eq_mul]
  have hkn (x : P) (u : E) (hu : u ∈ k.ker) : α x u ∈ k.ker := by
    let xd : D := ⟨x.val.val,x.property⟩
    have hj : j (α x u) = xd * j u * xd⁻¹ := rfl
    change q (j (α x u)) = 1
    rw [hj,map_mul,map_mul,map_inv]
    have hku : q (j u) = 1 := hu
    rw [hku,mul_one,mul_inv_cancel]
  obtain ⟨hsize,_⟩ := Atlas.G2.Natural.BinaryPointFlag.fivePoint_image_card_le_two_of_point_action
    a ha P (θ (Additive.ofMul z)) hv hP α θ he k hkn
  have hcard : Nat.card (E ⊓ D.pCoreIn 2 : Subgroup Rudvalis.Model) = Nat.card k.ker := by
    rw [←hmap,card_map_of_injective E.subtype_injective]
  rcases hsize with hs | hs
  · exact hcard.trans hs
  · exfalso
    have hE : Nat.card E = 64 := by
      rw [Nat.card_congr d.toEquiv]
      have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
      rw [Nat.card_zmod,s.coordinates.finrank_eq,Atlas.G2.Natural.finrank_space] at hh
      exact hh
    have hi : E ⊓ D.pCoreIn 2 = E := eq_of_le_of_card_ge inf_le_left (by rw [hcard,hs,hE])
    have hclass : IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) :=
      native_points s A hAN hcomm hodd hAV J mark hV hR z hz
    exact Rudvalis.PointCoreBound.elementary_not_le_point_core z hclass E hE (inf_eq_left.mp hi)

/-- The separate ambient S₅ quotient has kernel order 1024 and image D₁₂. -/
theorem unitary_terminal_native_ambient_point_order (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (mark : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map mark.toMonoidHom
    let C := normalizer (E : Set Rudvalis.Model)
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      let P := D.subgroupOf C
      ∃ q : D →* Equiv.Perm (Fin 5),
        Function.Surjective q ∧ q.ker = pCore 2 D ∧
        let i : P →* D := {
          toFun := fun x => ⟨x.val.val,x.property⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
        let r := q.comp i
        r.ker = ((D.pCoreIn 2).subgroupOf C).subgroupOf P ∧
        r.ker.map (C.subtype.comp P.subtype) = C ⊓ D.pCoreIn 2 ∧
        Nat.card r.ker = 1024 ∧ Nat.card r.range = 12 ∧
        ∃ t : Equiv.Perm (Fin 5), t.IsSwap ∧
          ((E.subgroupOf C).subgroupOf P).map r = zpowers t ∧
          r.range = centralizer ({t} : Set (Equiv.Perm (Fin 5))) ∧
          Nonempty ((P ⧸ r.ker) ≃* DihedralGroup 6) ∧ ⁅pCore 2 P,⊤⁆ ≤ r.ker := by
  let E := (V.subgroupOf J).map mark.toMonoidHom
  let C := normalizer (E : Set Rudvalis.Model)
  have hcent : C ⊓ centralizer (E : Set Rudvalis.Model) = E := by
    rw [(unitary_terminal_native_centralizer s A hAN hcomm hodd hAV J mark hV hR).2.2.2.2.2.2.2]
    exact inf_eq_right.mpr E.le_normalizer
  have hEC : E ≤ C := hcent.ge.trans inf_le_left
  have hEcentral : E ≤ centralizer (E : Set Rudvalis.Model) := hcent.ge.trans inf_le_right
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  let P := D.subgroupOf C
  have hED : E ≤ D := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact (mem_centralizer_iff.mp (hEcentral hu) z z.property).symm
  have hclass : IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) :=
    native_points s A hAN hcomm hodd hAV J mark hV hR z hz
  have hPcard : Nat.card P = 12288 :=
    (native_sizes s A hAN hcomm hodd hAV J mark hV hR).2 z hz
  have hintersect : Nat.card (E ⊓ D.pCoreIn 2 : Subgroup Rudvalis.Model) = 32 :=
    unitary_terminal_native_module_core_intersection s A hAN hcomm hodd hAV J mark hV hR z hz
  obtain ⟨a,d,ha,hker,_,he,hCcard,hpoint⟩ :=
    unitary_terminal_native_full_action s A hAN hcomm hodd hAV J mark hV hR
  have hCE : C ≤ normalizer (E : Set Rudvalis.Model) := le_rfl
  have hv : s.coordinates (Additive.ofMul (d z)) ≠ 0 := by
    intro hh
    apply hz
    apply d.injective
    apply Additive.ofMul.injective
    apply s.coordinates.injective
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates (Additive.ofMul (d 1))
    rw [map_one]
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates 0
    rw [map_zero]
    exact hh
  have hP (x : C) : x ∈ P ↔ Atlas.G2.Natural.action (ZMod 2) (a x)
      (s.coordinates (Additive.ofMul (d z))) = s.coordinates (Additive.ofMul (d z)) := by
    rw [←he x z,s.coordinates.injective.eq_iff,Additive.ofMul.injective.eq_iff,d.injective.eq_iff]
    change (x : Rudvalis.Model) ∈ centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model) ↔ _
    rw [mem_centralizer_singleton_iff,Subtype.ext_iff]
    change (x : Rudvalis.Model)*(z : Rudvalis.Model) = (z : Rudvalis.Model)*(x : Rudvalis.Model) ↔
      (x : Rudvalis.Model)*(z : Rudvalis.Model)*(x : Rudvalis.Model)⁻¹ = (z : Rudvalis.Model)
    rw [mul_inv_eq_iff_eq_mul]
  obtain ⟨g,b,hb,hbk,hmark⟩ := Atlas.G2.Natural.BinaryPointFlag.exists_point_parabolic_map
    a ha P (s.coordinates (Additive.ofMul (d z))) hv hP
  rw [hker] at hbk

  have hcore : Nat.card (pCore 2 Atlas.G2.BinaryCore.secondParabolic) = 32 := by
    rw [←Atlas.G2.LieParabolicSetup.local₂_binary]
    exact Atlas.G2.LieParabolicSetup.card_local₂_pCore_binary
  exact Rudvalis.point_core_intersection_exact C E hEC z hED hclass hPcard hintersect
    b hb hbk Atlas.G2.BinaryCore.secondParabolic_card hcore

/-- A point-stabilizer-invariant three-space lies in the ambient core commutator. -/
theorem unitary_terminal_native_invariant_three (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (mark : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map mark.toMonoidHom
    let C := normalizer (E : Set Rudvalis.Model)
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      ∀ U : Subgroup Rudvalis.Model, U ≤ E → Nat.card U = 8 →
        C ⊓ D ≤ normalizer (U : Set Rudvalis.Model) →
        U ≤ ⁅D.pCoreIn 2,D.pCoreIn 2⁆ := by
  let E := (V.subgroupOf J).map mark.toMonoidHom
  let C := normalizer (E : Set Rudvalis.Model)
  obtain ⟨a,d,ha,hker,_,he,hCcard,hpoint⟩ :=
    unitary_terminal_native_full_action s A hAN hcomm hodd hAV J mark hV hR
  have hCE : C ≤ normalizer (E : Set Rudvalis.Model) := le_rfl
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective d.symm.toMonoidHom d.symm.surjective
  have hNC : normalizer (E : Set Rudvalis.Model) = C := rfl
  have hEC : E ≤ C := E.le_normalizer.trans hNC.le
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  let P := D.subgroupOf C
  have hED : E ≤ D := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact setLike_mul_comm hu z.property
  have hEP : E.subgroupOf C ≤ P := fun _ hx => hED hx
  have hv : s.coordinates (Additive.ofMul (d z)) ≠ 0 := by
    intro hh
    apply hz
    apply d.injective
    apply Additive.ofMul.injective
    apply s.coordinates.injective
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates (Additive.ofMul (d 1))
    rw [map_one]
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates 0
    rw [map_zero]
    exact hh
  have hP (x : C) : x ∈ P ↔ Atlas.G2.Natural.action (ZMod 2) (a x)
      (s.coordinates (Additive.ofMul (d z))) = s.coordinates (Additive.ofMul (d z)) := by
    rw [←he x z,s.coordinates.injective.eq_iff,Additive.ofMul.injective.eq_iff,d.injective.eq_iff]
    change (x : Rudvalis.Model) ∈ centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model) ↔ _
    rw [mem_centralizer_singleton_iff,Subtype.ext_iff]
    change (x : Rudvalis.Model)*(z : Rudvalis.Model) = (z : Rudvalis.Model)*(x : Rudvalis.Model) ↔
      (x : Rudvalis.Model)*(z : Rudvalis.Model)*(x : Rudvalis.Model)⁻¹ = (z : Rudvalis.Model)
    rw [mul_inv_eq_iff_eq_mul]
  obtain ⟨g,b,hb,hbk,hmark⟩ := Atlas.G2.Natural.BinaryPointFlag.exists_point_parabolic_map
    a ha P (s.coordinates (Additive.ofMul (d z))) hv hP
  rw [hker] at hbk
  have hPcard : Nat.card P = 12288 :=
    (native_sizes s A hAN hcomm hodd hAV J mark hV hR).2 z hz
  have hbcard : Nat.card b.ker = 64 := by
    have hm := b.ker.card_mul_index
    rw [index_ker,b.range_eq_top_of_surjective hb,card_top,
      Atlas.G2.BinaryCore.secondParabolic_card] at hm
    change Nat.card b.ker * 192 = Nat.card P at hm
    rw [hPcard] at hm
    omega
  obtain ⟨q,hq,hqk,hrk,hrmap,hrcard,_,t,ht,htE,htR,_,hrcomm⟩ :=
    unitary_terminal_native_ambient_point_order s A hAN hcomm hodd hAV J mark hV hR z hz
  let i : P →* D := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let r := q.comp i
  let j := C.subtype.comp P.subtype
  have hj : Function.Injective j := C.subtype_injective.comp P.subtype_injective
  have hbmap : b.ker.map j = E := by
    rw [hbk,←map_map,map_subgroupOf_eq_of_le hEP,map_subgroupOf_eq_of_le hEC]
  have hinter : Nat.card (b.ker ⊓ r.ker : Subgroup P) = 32 := by
    rw [←card_map_of_injective hj,map_inf _ _ _ hj,hbmap,hrmap,
      ←inf_assoc,inf_eq_left.mpr hEC]
    exact unitary_terminal_native_module_core_intersection
      s A hAN hcomm hodd hAV J mark hV hR z hz

  have hrTwo : IsPGroup 2 r.ker := IsPGroup.of_card (n := 10) hrcard
  let k : b.ker →* E := (j.comp b.ker.subtype).codRestrict E
    (fun v => hbk.le v.property)
  have hk : Function.Bijective k := by
    constructor
    · intro u v h
      have hh : j (u : P) = j (v : P) := congrArg (fun v : E => (v : Rudvalis.Model)) h
      exact Subtype.ext (hj hh)
    · intro u
      let up : P := ⟨⟨u,hEC u.property⟩,hED u.property⟩
      exact ⟨⟨up,hbk.ge u.property⟩,rfl⟩
  let kd := (MulEquiv.ofBijective k hk).trans d
  have hkd (x : P) (v : b.ker) :
      s.coordinates (Additive.ofMul (kd ⟨x * v * x⁻¹,
        (inferInstance : b.ker.Normal).conj_mem v v.property x⟩)) =
      Atlas.G2.Natural.action (ZMod 2) (a (x : C))
        (s.coordinates (Additive.ofMul (kd v))) := by
    have hkconj : k ⟨x * v * x⁻¹,
        (inferInstance : b.ker.Normal).conj_mem v v.property x⟩ =
        E.normalizerMonoidHom (inclusion hCE (x : C)) (k v) := by
      apply Subtype.ext
      rfl
    change s.coordinates (Additive.ofMul (d (k _))) = _
    rw [hkconj,he]
    rfl
  intro U hUE hUcard hUn
  let U' := (U.subgroupOf C).subgroupOf P
  have hUP : U.subgroupOf C ≤ P := fun _ hu => hED (hUE hu)
  have hUC := hUE.trans hEC
  let : U'.Normal := ⟨fun u hu x => (mem_normalizer_iff.mp (hUn ⟨x.val.property,x.property⟩) u.val.val).mp hu⟩
  have hUker : U' ≤ b.ker := fun _ hu => hbk.ge (hUE hu)
  have hU'card : Nat.card U' = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv,hUcard]
  have hbound := Atlas.G2.Natural.BinaryPointFlag.invariant_three_le_second_kernel_commutator_of_marking
    b hb kd s.coordinates (a.comp P.subtype) g hmark hkd
    r.ker hrTwo hrcard
      ((congrArg (fun A : Subgroup P => Nat.card A) (inf_comm r.ker b.ker)).trans hinter)
      U' hUker hU'card
  have hm := map_mono (f := j) hbound
  have hUmap : U'.map j = U := by
    rw [←map_map,map_subgroupOf_eq_of_le hUP,map_subgroupOf_eq_of_le hUC]
  rw [hUmap,map_commutator,hrmap] at hm
  exact hm.trans (commutator_mono inf_le_right inf_le_right)

private theorem marked_point_kernel_chart
    {N : Type*} [Group N] (E C : Subgroup N)
    (hCE : C ≤ normalizer (E : Set N)) (a : C →* Full)
    (coord : E → Atlas.G2.Natural.Space (ZMod 2)) (hci : Function.Injective coord)
    (he : ∀ (x : C) (v : E),
      coord (E.normalizerMonoidHom (inclusion hCE x) v) =
        Atlas.G2.Natural.action (ZMod 2) (a x) (coord v))
    (P : Subgroup C) (b : P →* Atlas.G2.BinaryCore.secondParabolic)
    (hbk : b.ker = (E.subgroupOf C).subgroupOf P)
    (g : Full) (hmark : ∀ x : P, (b x : Full) = g * a x * g⁻¹) :
    ∃ coords : b.ker → Atlas.G2.Natural.Space (ZMod 2), Function.Injective coords ∧
      ∀ (x : P) (v : b.ker), x * (v : P) = (v : P) * x →
        Atlas.G2.Natural.action (ZMod 2) (b x : Full) (coords v) = coords v := by
  let j := C.subtype.comp P.subtype
  have hj : Function.Injective j := C.subtype_injective.comp P.subtype_injective
  let k : b.ker →* E := (j.comp b.ker.subtype).codRestrict E
    (fun v => hbk.le v.property)
  have hk : Function.Injective k := by
    intro u v h
    apply b.ker.subtype_injective
    apply hj
    exact congrArg (fun v : E => (v : N)) h
  have hg : Function.Injective (Atlas.G2.Natural.action (ZMod 2) g) := by
    apply Function.HasLeftInverse.injective
    refine ⟨Atlas.G2.Natural.action (ZMod 2) g⁻¹,?_⟩
    intro v
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  let coords : b.ker → Atlas.G2.Natural.Space (ZMod 2) := fun v =>
    Atlas.G2.Natural.action (ZMod 2) g (coord (k v))
  refine ⟨coords,hg.comp (hci.comp hk),?_⟩
  intro x v hcommute
  have hvfix : E.normalizerMonoidHom (inclusion hCE (x : C)) (k v) = k v := by
    apply Subtype.ext
    change j x * j (v : P) * (j x)⁻¹ = j (v : P)
    have hh := congrArg j hcommute
    rw [map_mul,map_mul] at hh
    rw [hh,mul_inv_cancel_right]
  have hax : Atlas.G2.Natural.action (ZMod 2) (a (x : C)) (coord (k v)) = coord (k v) :=
    (he (x : C) (k v)).symm.trans (congrArg coord hvfix)
  dsimp only [coords]
  rw [hmark]
  simp only [←Module.End.mul_apply,←map_mul]
  have heq : g * a (x : C) * g⁻¹ * g = g * a (x : C) := by group
  rw [heq,map_mul,Module.End.mul_apply,hax]


/-- A cubic fixes at most four elements of the ambient kernel intersection. -/
theorem unitary_terminal_native_cubic_intersection (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (mark : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map mark.toMonoidHom
    let C := normalizer (E : Set Rudvalis.Model)
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      let P := D.subgroupOf C
      ∃ x : P, orderOf x = 3 ∧
        Nat.card ((((D.pCoreIn 2).subgroupOf C).subgroupOf P) ⊓
          centralizer ({x} : Set P) : Subgroup P) ≤ 4 := by
  let E := (V.subgroupOf J).map mark.toMonoidHom
  let C := normalizer (E : Set Rudvalis.Model)
  obtain ⟨a,d,ha,hker,_,he,hCcard,hpoint⟩ :=
    unitary_terminal_native_full_action s A hAN hcomm hodd hAV J mark hV hR
  have hCE : C ≤ normalizer (E : Set Rudvalis.Model) := le_rfl
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective d.symm.toMonoidHom d.symm.surjective
  have hNC : normalizer (E : Set Rudvalis.Model) = C := rfl
  have hEC : E ≤ C := E.le_normalizer.trans hNC.le
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  let P := D.subgroupOf C
  have hED : E ≤ D := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact setLike_mul_comm hu z.property
  have hEP : E.subgroupOf C ≤ P := fun _ hx => hED hx
  have hv : s.coordinates (Additive.ofMul (d z)) ≠ 0 := by
    intro hh
    apply hz
    apply d.injective
    apply Additive.ofMul.injective
    apply s.coordinates.injective
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates (Additive.ofMul (d 1))
    rw [map_one]
    change s.coordinates (Additive.ofMul (d z)) = s.coordinates 0
    rw [map_zero]
    exact hh
  have hP (x : C) : x ∈ P ↔ Atlas.G2.Natural.action (ZMod 2) (a x)
      (s.coordinates (Additive.ofMul (d z))) = s.coordinates (Additive.ofMul (d z)) := by
    rw [←he x z,s.coordinates.injective.eq_iff,Additive.ofMul.injective.eq_iff,d.injective.eq_iff]
    change (x : Rudvalis.Model) ∈ centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model) ↔ _
    rw [mem_centralizer_singleton_iff,Subtype.ext_iff]
    change (x : Rudvalis.Model)*(z : Rudvalis.Model) = (z : Rudvalis.Model)*(x : Rudvalis.Model) ↔
      (x : Rudvalis.Model)*(z : Rudvalis.Model)*(x : Rudvalis.Model)⁻¹ = (z : Rudvalis.Model)
    rw [mul_inv_eq_iff_eq_mul]
  obtain ⟨g,b,hb,hbk,hmark⟩ := Atlas.G2.Natural.BinaryPointFlag.exists_point_parabolic_map
    a ha P (s.coordinates (Additive.ofMul (d z))) hv hP
  rw [hker] at hbk
  have hPcard : Nat.card P = 12288 :=
    (native_sizes s A hAN hcomm hodd hAV J mark hV hR).2 z hz
  have hbcard : Nat.card b.ker = 64 := by
    have hm := b.ker.card_mul_index
    rw [index_ker,b.range_eq_top_of_surjective hb,card_top,
      Atlas.G2.BinaryCore.secondParabolic_card] at hm
    change Nat.card b.ker * 192 = Nat.card P at hm
    rw [hPcard] at hm
    omega
  obtain ⟨q,hq,hqk,hrk,hrmap,hrcard,_,t,ht,htE,htR,_,hrcomm⟩ :=
    unitary_terminal_native_ambient_point_order s A hAN hcomm hodd hAV J mark hV hR z hz
  let i : P →* D := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let r := q.comp i
  let j := C.subtype.comp P.subtype
  have hj : Function.Injective j := C.subtype_injective.comp P.subtype_injective
  have hbmap : b.ker.map j = E := by
    rw [hbk,←map_map,map_subgroupOf_eq_of_le hEP,map_subgroupOf_eq_of_le hEC]
  have hinter : Nat.card (b.ker ⊓ r.ker : Subgroup P) = 32 := by
    rw [←card_map_of_injective hj,map_inf _ _ _ hj,hbmap,hrmap,
      ←inf_assoc,inf_eq_left.mpr hEC]
    exact unitary_terminal_native_module_core_intersection
      s A hAN hcomm hodd hAV J mark hV hR z hz
  have hnot : ¬ b.ker ≤ r.ker := by
    intro hh
    rw [inf_eq_left.mpr hh,hbcard] at hinter
    omega
  have hrTwo : IsPGroup 2 r.ker := IsPGroup.of_card (n := 10) hrcard
  have hbpre : b.ker = E.comap j := hbk
  let : IsElementaryAbelian 2 b.ker := hbpre.symm ▸
    IsElementaryAbelian.comap_of_injective j hj E
  obtain ⟨coords,hi,hfix⟩ := marked_point_kernel_chart E C hCE a
    (fun v : E => s.coordinates (Additive.ofMul (d v)))
    (s.coordinates.injective.comp (Additive.ofMul.injective.comp d.injective)) he P b hbk g hmark
  obtain ⟨x,hx,_,hbound⟩ := Atlas.G2.Natural.BinaryPointFlag.exists_cubic_kernel_intersection_fixed_card_le_four
    b hb hbcard coords hi hfix r.ker hrTwo hnot hrcomm
  refine ⟨x,hx,?_⟩
  rwa [hrk] at hbound

/-- The same cubic is Sylow in the full point centralizer and retains the bound. -/
theorem unitary_terminal_native_cubic_sylow (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (J : Subgroup G) (mark : J ≃* Rudvalis.Model)
    (hV : V ≤ J) (hR : oddActorResidual L A ≤ J) :
    let E := (V.subgroupOf J).map mark.toMonoidHom
    let C := normalizer (E : Set Rudvalis.Model)
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      ∃ X : Sylow 3 D,
        (X : Subgroup D).map D.subtype ≤ C ∧
        Nat.card ((D.pCoreIn 2 ⊓
          centralizer ((X : Subgroup D).map D.subtype : Set Rudvalis.Model)) ⊓ C :
            Subgroup Rudvalis.Model) ≤ 4 := by
  let E := (V.subgroupOf J).map mark.toMonoidHom
  let C := normalizer (E : Set Rudvalis.Model)
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  let P := D.subgroupOf C
  obtain ⟨x,hx,hbound⟩ :=
    unitary_terminal_native_cubic_intersection s A hAN hcomm hodd hAV J mark hV hR z hz
  let i : P →* D := {
    toFun := fun u => ⟨u.val.val,u.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro u v h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : D => (u : Rudvalis.Model)) h
  let Y := zpowers (i x)
  have hY : Nat.card Y = 3 := by
    rw [Nat.card_zpowers,orderOf_injective i hi,hx]
  have hclass : IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) :=
    native_points s A hAN hcomm hodd hAV J mark hV hR z hz
  have hD : Nat.card D = 245760 := Rudvalis.InvolutionCentralizers.first_centralizer_card hclass
  have hidx : ¬ 3 ∣ Y.index := by
    have hh := Y.card_mul_index
    rw [hY,hD] at hh
    have hi : Y.index = 81920 := by omega
    rw [hi]
    decide
  let X : Sylow 3 D := (IsPGroup.of_card (p := 3) (n := 1) hY).toSylow hidx
  let j := C.subtype.comp P.subtype
  have hj : Function.Injective j := C.subtype_injective.comp P.subtype_injective
  have hX : (X : Subgroup D).map D.subtype = zpowers (j x) := by
    change (zpowers (i x)).map D.subtype = _
    rw [MonoidHom.map_zpowers]
    rfl
  refine ⟨X,?_,?_⟩
  · rw [hX]
    exact zpowers_le.mpr x.val.property
  · rw [hX,zpowers_eq_closure,centralizer_closure]
    let R := ((D.pCoreIn 2).subgroupOf C).subgroupOf P
    have hm : (R ⊓ centralizer ({x} : Set P)).map j =
        (D.pCoreIn 2 ⊓ centralizer ({j x} : Set Rudvalis.Model)) ⊓ C := by
      ext y
      constructor
      · rintro ⟨u,hu,rfl⟩
        exact ⟨⟨hu.1,mem_centralizer_singleton_iff.mpr
          (by simpa only [map_mul] using congrArg j (mem_centralizer_singleton_iff.mp hu.2))⟩,
          u.val.property⟩
      · intro hy
        let u : P := ⟨⟨y,hy.2⟩,(pCoreIn_le 2 D) hy.1.1⟩
        refine ⟨u,⟨hy.1.1,?_⟩,rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        apply Subtype.ext
        exact mem_centralizer_singleton_iff.mp hy.1.2
    rw [←hm,card_map_of_injective hj]
    exact hbound

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
