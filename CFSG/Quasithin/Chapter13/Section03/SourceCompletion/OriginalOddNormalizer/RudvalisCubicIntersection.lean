module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisAmbientOrder
public import Theory.Representation.G2BinaryPointCubicFixed

/-!
# The original Rudvalis cubic intersection bound

The marked natural point parabolic supplies a cubic whose fixed space on
the original six-space has order at most four and whose two-core fixed
subgroup has order at most two. Kernel-image counting bounds the original
point stabilizer's two-core centralizer by eight. Coprime decomposition
supplies a fixed module element outside the ambient two-core intersection,
so the latter has cubic fixed subgroup of order at most four.

The same cubic is Sylow in the full ambient point centralizer, whose order
has exactly one factor of three. Mapping back through the literal subgroup
inclusions gives the bound on its two-core centralizer intersected with the
original normalizer image. The final theorem applies it to the original
odd-actor residual, preserving the relative Sylow placement, full module,
section-centralizer conjugation and central quotient marking.

This supplies the upper bound needed in the source's quaternion escape.
The quaternion identification, original three-space placement, J₄ exclusion
and terminal odd-normalizer control remain with qt-d-13316-source; earlier
Structural1222 retains its final discharge with qt-theorem-d.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612, and 4.4.3, p.623,
in the original 13.3.16 application, pp.893--896.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

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

/-- A literal point-stabilizer cubic fixes at most four elements of the ambient kernel. -/
theorem unitary_original_pushingUp_rudvalis_cubic_intersection (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let E := ((W.subgroupOf H).subgroupOf K).map f
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      let P := D.subgroupOf C
      ∃ x : P, orderOf x = 3 ∧
        Nat.card ((((D.pCoreIn 2).subgroupOf C).subgroupOf P) ⊓
          centralizer ({x} : Set P) : Subgroup P) ≤ 4 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let E := ((W.subgroupOf H).subgroupOf K).map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  obtain ⟨hCE,a,d,ha,hker,_,he⟩ :=
    unitary_original_pushingUp_rudvalis_full_action s hcover hJH hc K hK e c hVW
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective d.symm.toMonoidHom d.symm.surjective
  have hNC : normalizer (E : Set Rudvalis.Model) = C :=
    (unitary_original_pushingUp_rudvalis_exact_sizes s hcover hJH hc K hK e c hVW).1
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
    (unitary_original_pushingUp_rudvalis_exact_sizes s hcover hJH hc K hK e c hVW).2.2 z hz
  have hbcard : Nat.card b.ker = 64 := by
    have hm := b.ker.card_mul_index
    rw [index_ker,b.range_eq_top_of_surjective hb,card_top,
      Atlas.G2.BinaryCore.secondParabolic_card] at hm
    change Nat.card b.ker * 192 = Nat.card P at hm
    rw [hPcard] at hm
    omega
  obtain ⟨q,hq,hqk,hrk,hrmap,hrcard,_,t,ht,htE,htR,_,hrcomm⟩ :=
    unitary_original_pushingUp_rudvalis_ambient_point_order s hcover hJH hc K hK e c hVW z hz
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
    exact unitary_original_pushingUp_rudvalis_module_core_intersection
      s hcover hJH hc K hK e c hVW z hz
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

/-- The cubic can be chosen as a Sylow subgroup of the full ambient point
centralizer. Its fixed points in the ambient two-core meet the original
normalizer image in order at most four. -/
theorem unitary_original_pushingUp_rudvalis_cubic_sylow (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let E := ((W.subgroupOf H).subgroupOf K).map f
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    ∀ z : E, z ≠ 1 →
      let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
      ∃ X : Sylow 3 D,
        (X : Subgroup D).map D.subtype ≤ C ∧
        Nat.card ((D.pCoreIn 2 ⊓
          centralizer ((X : Subgroup D).map D.subtype : Set Rudvalis.Model)) ⊓ C :
            Subgroup Rudvalis.Model) ≤ 4 := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let E := ((W.subgroupOf H).subgroupOf K).map f
  let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
  dsimp only
  intro z hz
  let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
  let P := D.subgroupOf C
  obtain ⟨x,hx,hbound⟩ :=
    unitary_original_pushingUp_rudvalis_cubic_intersection s hcover hJH hc K hK e c hVW z hz
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
    ((unitary_original_pushingUp_rudvalis_module_and_points s hcover hJH hc K hK e c hVW).2.2 z hz).2.1
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


/-- The cubic centralizer bound in the original escaping odd-actor component,
with its literal relative Sylow, full module and central quotient marking. -/
theorem unitary_original_oddActorResidual_cubic_sylow (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
      (c : sectionCentralizerIn (normalizer (L : Set G)) L),
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        Y (J.pCoreIn 2) W ∧
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
        (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W ∧
      ∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          ∃ e : K ⧸ center K ≃* Rudvalis.Model,
            W = V.map (MulAut.conj (c : G)).toMonoidHom ∧
            let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let E := ((W.subgroupOf H).subgroupOf K).map f
            let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
            ∀ z : E, z ≠ 1 →
              let D := centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)
              ∃ X : Sylow 3 D,
                (X : Subgroup D).map D.subtype ≤ C ∧
                Nat.card ((D.pCoreIn 2 ⊓
                  centralizer ((X : Subgroup D).map D.subtype : Set Rudvalis.Model)) ⊓ C :
                    Subgroup Rudvalis.Model) ≤ 4) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,_,_,⟨K,hK,hout,n,hn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hcS,hcV,K,hK,hout,?_⟩
  rcases hn with rfl | rfl
  · exact Or.inl ⟨e⟩
  · apply Or.inr
    have hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) := by
      have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
      obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
        A hAN hcomm hodd hAV
      have hi : oddActorResidual L A ≤ J :=
        ((le_inf le_rfl ((oddActorResidual_le L A).trans inf_le_left)).trans hpush.2).trans
          inf_le_left
      exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
    exact ⟨e,unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_cubic_sylow s hcover hJH hc K hK e c hcV⟩



end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
