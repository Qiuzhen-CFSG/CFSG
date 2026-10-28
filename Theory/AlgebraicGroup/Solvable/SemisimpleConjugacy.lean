module

public import Theory.AlgebraicGroup.Unipotent.SemisimpleCommutator
public import Theory.AlgebraicGroup.Tori.Character.Image

/-!
# Semisimple conjugacy in a solvable torus-unipotent product

This module proves the conjugacy step in A. Borel, *Linear Algebraic Groups*,
Chapter 3, Theorem 10.6(4). If a closed subtorus `T` and a connected normal
unipotent closed subgroup `U` satisfy `G = T * U` on points, every semisimple
point of `G` is conjugate into `T` by a point of `U`. This formulation isolates
the result needed by a supplied torus complement and avoids any appeal to
maximal-torus conjugacy.

The proof is a strong induction on `dim U`. In positive dimension, the identity
component `N` of the center of `U` is connected, positive-dimensional, central
in `U`, and normal in `G`. The quotient `G/N` again has the required torus and
unipotent factors, while its unipotent factor has smaller dimension. After
lifting the quotient conjugator, the remaining error lies in `N`. Proposition
9.3's public `semisimpleCommutator_factorization` writes that error as a
semisimple commutator times a fixed point. Centrality makes this a Jordan
decomposition, so uniqueness forces the unipotent fixed point to be trivial.
-/

open Theory.AlgebraicGroup

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open scoped Pointwise

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma closedSubgroup_carrier_isConnected_local
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : _root_.IsConnected (H : Set (Variety.Point G))) :
    Variety.IsConnected H.carrierVariety := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    Subtype.connectedSpace hH
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    e.connectedSpace_iff.mpr inferInstance
  exact connectedSpace_iff_univ.mp inferInstance

omit [IsAlgClosed k] in
private lemma closedSubgroup_isConnected_of_carrier_local
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (hH : Variety.IsConnected H.carrierVariety) :
    _root_.IsConnected (H : Set (Variety.Point G)) := by
  let e := Variety.closedSubvarietyPointHomeomorph H.isZariskiClosed
  let : ConnectedSpace (Variety.Point H.carrierVariety) :=
    connectedSpace_iff_univ.mpr hH
  let : ConnectedSpace {x : Variety.Point G // x ∈ (H : Set (Variety.Point G))} :=
    e.connectedSpace_iff.mp inferInstance
  exact isConnected_iff_connectedSpace.mpr inferInstance

private lemma semisimpleElement_conjugate_local
    {G : Variety k} [AlgebraicGroup G] {s g : Variety.Point G}
    (hs : IsSemisimpleElement G s) :
    IsSemisimpleElement G (g * s * g⁻¹) := by
  let c : AlgebraicGroup.Morphism G G :=
    { toVariety := AlgebraicGroup.conjugationByMorphism G g
      map_one := by simp [AlgebraicGroup.conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp only [AlgebraicGroup.conjugationByMorphism_apply]
        group }
  have hc := morphism_preserves_semisimpleElement c s hs
  change IsSemisimpleElement G
    ((AlgebraicGroup.conjugationByMorphism G g).toFun s) at hc
  simpa [AlgebraicGroup.conjugationByMorphism_apply] using hc

/-- A semisimple point in a product of a subtorus and a connected normal
unipotent subgroup is conjugate into the subtorus by a point of the unipotent
subgroup. -/
public theorem semisimpleElement_conjugate_into_subtorus_of_unipotent_factorization
    {G : Variety k} [AlgebraicGroup G] (T U : ClosedSubgroup G)
    (hT : IsSubtorus T)
    (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (hUnormal : U.toSubgroup.Normal)
    (hfactor : ∀ x : Variety.Point G, ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u)
    (s : Variety.Point G) (hs : IsSemisimpleElement G s) :
    ∃ u : Variety.Point G, u ∈ U.toSubgroup ∧
      u⁻¹ * s * u ∈ T.toSubgroup := by
  induction hdim : Cardinal.toNat (Variety.dimension U.carrierVariety)
      using Nat.strong_induction_on generalizing G T U s with
  | h d ih =>
      by_cases hUdim : Variety.dimension U.carrierVariety = 0
      · have hUbot : U.toSubgroup = ⊥ := by
          by_contra hne
          have hpos := connected_closedSubgroup_dimension_pos_of_ne_bot
            U (closedSubgroup_isConnected_of_carrier_local U hUconn) hne
          rw [hUdim] at hpos
          exact (lt_irrefl 0 hpos)
        obtain ⟨t, u, ht, hu, hstu⟩ := hfactor s
        have huOne : u = 1 := by
          rw [hUbot] at hu
          simpa using hu
        refine ⟨1, U.toSubgroup.one_mem, ?_⟩
        simpa [hstu, huOne] using ht
      · have hUpos : 0 < Variety.dimension U.carrierVariety := by
          by_contra hpos
          exact hUdim (le_antisymm (not_lt.mp hpos) (by simp))
        let Z : ClosedSubgroup U.carrierVariety :=
          (ClosedSubgroup.top (G := U.carrierVariety)).centralizer
        letI : AlgebraicGroup Z.carrierVariety := Z.carrierAlgebraicGroup
        let j : AlgebraicGroup.Morphism Z.carrierVariety G :=
          U.inclusion.comp Z.inclusion
        let C : ClosedSubgroup G := j.imageClosedSubgroup
        have hj_apply (z : Variety.Point Z.carrierVariety) :
            j.onPoints z = U.inclusion.onPoints (Z.inclusion.onPoints z) := rfl
        have hCmem (x : Variety.Point G) : x ∈ C.toSubgroup ↔
            x ∈ U.toSubgroup ∧
              ∀ y ∈ U.toSubgroup, x * y = y * x := by
          constructor
          · intro hx
            change x ∈ j.image at hx
            obtain ⟨z, hz⟩ := hx
            have hzZ : Z.inclusion.onPoints z ∈ Z.toSubgroup :=
              (Z.pointEquiv z).property
            have hxU : x ∈ U.toSubgroup := by
              rw [← hz, hj_apply]
              exact (U.pointEquiv (Z.inclusion.onPoints z)).property
            refine ⟨hxU, ?_⟩
            intro y hy
            let yU := U.pointEquiv.symm ⟨y, hy⟩
            have hzy : yU * Z.inclusion.onPoints z =
                Z.inclusion.onPoints z * yU :=
              (Subgroup.mem_centralizer_iff.mp hzZ) yU (by trivial)
            have hzy' := congrArg U.inclusion.onPoints hzy
            rw [map_mul, map_mul] at hzy'
            have hyU : U.inclusion.onPoints yU = y := by
              change (U.pointEquiv yU).val = y
              simp [yU]
            rw [hyU, ← hj_apply, hz] at hzy'
            exact hzy'.symm
          · rintro ⟨hxU, hxcentral⟩
            let xU := U.pointEquiv.symm ⟨x, hxU⟩
            have hxIncl : U.inclusion.onPoints xU = x := by
              change (U.pointEquiv xU).val = x
              simp [xU]
            have hxZ : xU ∈ Z.toSubgroup := by
              change xU ∈ Subgroup.centralizer
                (Set.univ : Set (Variety.Point U.carrierVariety))
              rw [Subgroup.mem_centralizer_iff]
              intro y _
              apply U.inclusion_injective
              rw [map_mul, map_mul, hxIncl]
              exact (hxcentral _ (U.pointEquiv y).property).symm
            let z := Z.pointEquiv.symm ⟨xU, hxZ⟩
            change x ∈ j.image
            refine ⟨z, ?_⟩
            rw [hj_apply]
            change U.inclusion.onPoints (Z.pointEquiv z).val = x
            simp [z, hxIncl]
        have hjinj : Function.Injective j.onPoints :=
          U.inclusion_injective.comp Z.inclusion_injective
        letI : Subsingleton j.kernelClosedSubgroup.toSubgroup := by
          constructor
          intro x y
          apply Subtype.ext
          apply hjinj
          rw [x.property, y.property]
        letI : Subsingleton (Variety.Point j.kernelClosedSubgroup.carrierVariety) :=
          j.kernelClosedSubgroup.pointEquiv.subsingleton
        letI : Finite (Variety.Point j.kernelClosedSubgroup.carrierVariety) :=
          Finite.of_subsingleton
        have hjkerDim : Variety.dimension j.kernelClosedSubgroup.carrierVariety = 0 :=
          (dimension_zero_iff_finite_points
            j.kernelClosedSubgroup.carrierVariety).2 inferInstance
        have hjdim := morphism_dimension_eq_kernel_add_image j
        rw [hjkerDim, zero_add] at hjdim
        have hZpos : 0 < Variety.dimension Z.carrierVariety := by
          simpa only [Z] using unipotent_positiveCenter_dimension hU hUpos
        have hCpos : 0 < Variety.dimension C.carrierVariety := by
          change 0 < Variety.dimension j.imageClosedSubgroup.carrierVariety
          rw [← hjdim]
          exact hZpos
        have hCnormal : C.toSubgroup.Normal := by
          refine ⟨?_⟩
          intro x hx g
          obtain ⟨hxU, hxcentral⟩ := (hCmem x).mp hx
          apply (hCmem _).mpr
          refine ⟨hUnormal.conj_mem x hxU g, ?_⟩
          intro y hy
          have hyback : g⁻¹ * y * g ∈ U.toSubgroup := by
            simpa only [inv_inv] using hUnormal.conj_mem y hy g⁻¹
          have hc := hxcentral _ hyback
          have hc' := congrArg (fun z ↦ g * z * g⁻¹) hc
          simpa [mul_assoc] using hc'
        let N : ClosedSubgroup G := C.identityComponentAmbient
        have hNconnSet : _root_.IsConnected (N : Set (Variety.Point G)) :=
          C.identityComponentAmbient_isConnected
        have hNconn : Variety.IsConnected N.carrierVariety :=
          closedSubgroup_carrier_isConnected_local N hNconnSet
        have hNC : N ≤ C := C.identityComponentAmbient_le
        have hNU : N ≤ U := by
          intro n hn
          exact (hCmem n).mp (hNC hn) |>.1
        have hNcentral : ∀ n ∈ N.toSubgroup, ∀ u ∈ U.toSubgroup,
            n * u = u * n := by
          intro n hn
          exact (hCmem n).mp (hNC hn) |>.2
        have hNunipotent : IsUnipotentAlgebraicGroup N.carrierVariety := by
          intro n
          let g := N.inclusion.onPoints n
          have hgN : g ∈ N.toSubgroup := (N.pointEquiv n).property
          have hgU : g ∈ U.toSubgroup := hNU hgN
          let u := U.pointEquiv.symm ⟨g, hgU⟩
          have huAmb : IsUnipotentElement G g := by
            have hu := morphism_preserves_unipotentElement U.inclusion u (hU u)
            have huIncl : U.inclusion.onPoints u = g := by
              change (U.pointEquiv u).val = g
              simp [u]
            rwa [huIncl] at hu
          have hn := closedSubgroup_unipotent_of_ambient N hgN huAmb
          have heq : N.pointEquiv.symm ⟨g, hgN⟩ = n := by
            apply N.pointEquiv.injective
            apply Subtype.ext
            rfl
          rwa [heq] at hn
        have hNnormal : N.toSubgroup.Normal :=
          C.identityComponentAmbient_normal_of_normal hCnormal
        have hNpos : 0 < Variety.dimension N.carrierVariety := by
          rw [ClosedSubgroup.dimension_identityComponentAmbient]
          exact hCpos
        obtain ⟨Q, hQ, q, hqsurj, hqker, _⟩ := theorem_1_1_2_b N hNnormal
        letI : AlgebraicGroup Q := hQ
        let fT : AlgebraicGroup.Morphism T.carrierVariety Q := q.comp T.inclusion
        let TQ : ClosedSubgroup Q := fT.imageClosedSubgroup
        letI : AlgebraicGroup TQ.carrierVariety := TQ.carrierAlgebraicGroup
        have hTQ : IsSubtorus TQ := morphism_image_isTorus fT hT
        let fU : AlgebraicGroup.Morphism U.carrierVariety Q := q.comp U.inclusion
        let UQ : ClosedSubgroup Q := fU.imageClosedSubgroup
        letI : AlgebraicGroup UQ.carrierVariety := UQ.carrierAlgebraicGroup
        have hfU_mem (u : Variety.Point U.carrierVariety) :
            fU.onPoints u ∈ UQ.toSubgroup := ⟨u, rfl⟩
        let pU : AlgebraicGroup.Morphism U.carrierVariety UQ.carrierVariety :=
          fU.codRestrictClosedSubgroup UQ hfU_mem
        have hpU_surj : Function.Surjective pU.onPoints :=
          fU.codRestrictImageClosedSubgroup_surjective hfU_mem
        have hUQconn : Variety.IsConnected UQ.carrierVariety :=
          closedSubgroup_carrier_isConnected_local UQ
            (fU.imageClosedSubgroup_isConnected hUconn)
        have hUQuni : IsUnipotentAlgebraicGroup UQ.carrierVariety :=
          hU.of_surjective pU hpU_surj
        have hUQnormal : UQ.toSubgroup.Normal := by
          refine ⟨?_⟩
          intro x hx y
          change x ∈ fU.image at hx
          obtain ⟨u, rfl⟩ := hx
          obtain ⟨g, rfl⟩ := hqsurj y
          have hconj : g * U.inclusion.onPoints u * g⁻¹ ∈ U.toSubgroup :=
            hUnormal.conj_mem _ (U.pointEquiv u).property g
          let u' := U.pointEquiv.symm
            ⟨g * U.inclusion.onPoints u * g⁻¹, hconj⟩
          change q.onPoints g * fU.onPoints u * (q.onPoints g)⁻¹ ∈ fU.image
          refine ⟨u', ?_⟩
          change q.onPoints (U.inclusion.onPoints u') =
            q.onPoints g * q.onPoints (U.inclusion.onPoints u) *
              (q.onPoints g)⁻¹
          rw [← map_mul, ← map_inv, ← map_mul]
          apply congrArg q.onPoints
          change (U.pointEquiv u').val = _
          simp [u']
        have hfactorQ : ∀ x : Variety.Point Q, ∃ t u,
            t ∈ TQ.toSubgroup ∧ u ∈ UQ.toSubgroup ∧ x = t * u := by
          intro x
          obtain ⟨g, rfl⟩ := hqsurj x
          obtain ⟨t, u, ht, hu, htu⟩ := hfactor g
          let tT := T.pointEquiv.symm ⟨t, ht⟩
          let uU := U.pointEquiv.symm ⟨u, hu⟩
          refine ⟨fT.onPoints tT, fU.onPoints uU, ⟨tT, rfl⟩,
            ⟨uU, rfl⟩, ?_⟩
          change q.onPoints g =
            q.onPoints (T.inclusion.onPoints tT) *
              q.onPoints (U.inclusion.onPoints uU)
          rw [← map_mul]
          apply congrArg q.onPoints
          rw [htu]
          change t * u = (T.pointEquiv tT).val * (U.pointEquiv uU).val
          simp [tT, uU]
        have hfU_one_iff (u : Variety.Point U.carrierVariety) :
            fU.onPoints u = 1 ↔ U.inclusion.onPoints u ∈ N.toSubgroup := by
          change q.onPoints (U.inclusion.onPoints u) = 1 ↔ _
          rw [← MonoidHom.mem_ker]
          change U.inclusion.onPoints u ∈ q.kernel ↔ _
          rw [hqker]
        let nU : AlgebraicGroup.Morphism N.carrierVariety U.carrierVariety :=
          N.inclusion.codRestrictClosedSubgroup U fun n ↦
            hNU (N.pointEquiv n).property
        have hnU_apply (n : Variety.Point N.carrierVariety) :
            U.inclusion.onPoints (nU.onPoints n) = N.inclusion.onPoints n :=
          AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply
            N.inclusion U (fun n ↦ hNU (N.pointEquiv n).property) n
        have hnUinj : Function.Injective nU.onPoints := by
          intro x y hxy
          apply N.inclusion_injective
          rw [← hnU_apply, ← hnU_apply, hxy]
        let I : ClosedSubgroup U.carrierVariety := nU.imageClosedSubgroup
        have hIconn : Variety.IsConnected I.carrierVariety :=
          closedSubgroup_carrier_isConnected_local I
            (nU.imageClosedSubgroup_isConnected hNconn)
        have hIdim : Variety.dimension I.carrierVariety =
            Variety.dimension N.carrierVariety := by
          letI : Subsingleton nU.kernelClosedSubgroup.toSubgroup := by
            constructor
            intro x y
            apply Subtype.ext
            apply hnUinj
            rw [x.property, y.property]
          letI : Subsingleton
              (Variety.Point nU.kernelClosedSubgroup.carrierVariety) :=
            nU.kernelClosedSubgroup.pointEquiv.subsingleton
          letI : Finite (Variety.Point nU.kernelClosedSubgroup.carrierVariety) :=
            Finite.of_subsingleton
          have hker0 : Variety.dimension nU.kernelClosedSubgroup.carrierVariety = 0 :=
            (dimension_zero_iff_finite_points
              nU.kernelClosedSubgroup.carrierVariety).2 inferInstance
          have hdim' := morphism_dimension_eq_kernel_add_image nU
          rw [hker0, zero_add] at hdim'
          exact hdim'.symm
        have hIle : I ≤ fU.kernelClosedSubgroup := by
          intro x hx
          change x ∈ nU.image at hx
          obtain ⟨n, rfl⟩ := hx
          change fU.onPoints (nU.onPoints n) = 1
          rw [hfU_one_iff, hnU_apply]
          exact (N.pointEquiv n).property
        have hkerPos : 0 <
            Variety.dimension fU.kernelClosedSubgroup.carrierVariety := by
          have hIconnSet : _root_.IsConnected
              (I : Set (Variety.Point U.carrierVariety)) :=
            closedSubgroup_isConnected_of_carrier_local I hIconn
          have hle := connected_closedSubgroup_dimension_le_of_le
            I fU.kernelClosedSubgroup hIconnSet hIle
          rw [hIdim] at hle
          exact hNpos.trans_le hle
        have hUQdimlt : Variety.dimension UQ.carrierVariety <
            Variety.dimension U.carrierVariety := by
          have hformula := morphism_dimension_eq_kernel_add_image fU
          have hnat := congrArg Cardinal.toNat hformula
          rw [Cardinal.toNat_add
            (variety_dimension_lt_aleph0 fU.kernelClosedSubgroup.carrierVariety)
            (variety_dimension_lt_aleph0 fU.imageClosedSubgroup.carrierVariety)] at hnat
          have hkerNatPos : 0 < Cardinal.toNat
              (Variety.dimension fU.kernelClosedSubgroup.carrierVariety) :=
            Cardinal.toNat_pos.mpr ⟨hkerPos.ne',
              variety_dimension_lt_aleph0 fU.kernelClosedSubgroup.carrierVariety⟩
          apply (Cardinal.toNat_lt_iff_lt_of_lt_aleph0
            (variety_dimension_lt_aleph0 UQ.carrierVariety)
            (variety_dimension_lt_aleph0 U.carrierVariety)).mp
          change Cardinal.toNat
              (Variety.dimension fU.imageClosedSubgroup.carrierVariety) < _
          omega
        have hUQnatlt : Cardinal.toNat
            (Variety.dimension UQ.carrierVariety) < d := by
          rw [← hdim]
          exact Cardinal.toNat_lt_toNat hUQdimlt
            (variety_dimension_lt_aleph0 U.carrierVariety)
        have hqs : IsSemisimpleElement Q (q.onPoints s) :=
          morphism_preserves_semisimpleElement q s hs
        obtain ⟨uq, huqUQ, huqTQ⟩ :=
          ih _ hUQnatlt TQ UQ hTQ hUQconn hUQuni hUQnormal hfactorQ
            (q.onPoints s) hqs rfl
        change uq ∈ fU.image at huqUQ
        obtain ⟨uU, huUEq⟩ := huqUQ
        let uG := U.inclusion.onPoints uU
        have huG : uG ∈ U.toSubgroup := (U.pointEquiv uU).property
        let s₁ := uG⁻¹ * s * uG
        have hs₁Semi : IsSemisimpleElement G s₁ := by
          simpa [s₁] using
            (semisimpleElement_conjugate_local (g := uG⁻¹) hs)
        have hqs₁ : q.onPoints s₁ = uq⁻¹ * q.onPoints s * uq := by
          change fU.onPoints uU = uq at huUEq
          change q.onPoints (U.inclusion.onPoints uU) = uq at huUEq
          simp only [s₁, map_mul, map_inv, uG]
          rw [huUEq]
        have hqs₁TQ : q.onPoints s₁ ∈ TQ.toSubgroup := by
          rw [hqs₁]
          exact huqTQ
        change q.onPoints s₁ ∈ fT.image at hqs₁TQ
        obtain ⟨tT, htTEq⟩ := hqs₁TQ
        let tG := T.inclusion.onPoints tT
        have htG : tG ∈ T.toSubgroup := (T.pointEquiv tT).property
        have htSemi : IsSemisimpleElement G tG :=
          morphism_preserves_semisimpleElement T.inclusion tT (hT.all_semisimple tT)
        let nG := s₁ * tG⁻¹
        have hqnG : q.onPoints nG = 1 := by
          simp only [nG, map_mul, map_inv]
          change q.onPoints s₁ * (fT.onPoints tT)⁻¹ = 1
          rw [htTEq]
          group
        have hnG : nG ∈ N.toSubgroup := by
          rw [← hqker]
          exact hqnG
        let nN := N.pointEquiv.symm ⟨nG, hnG⟩
        have hnN_apply : N.inclusion.onPoints nN = nG := by
          change (N.pointEquiv nN).val = nG
          simp [nN]
        have hs₁eq : s₁ = nG * tG := by
          simp [nG]
        have htNorm : tG ∈
            Subgroup.normalizer (N.toSubgroup : Set (Variety.Point G)) := by
          apply Subgroup.mem_normalizer_iff.mpr
          intro x
          constructor
          · exact fun hx ↦ hNnormal.conj_mem x hx tG
          · intro hx
            have hback := hNnormal.conj_mem (tG * x * tG⁻¹) hx tG⁻¹
            simpa [mul_assoc] using hback
        obtain ⟨hdecomp, _⟩ :=
          semisimpleCommutator_factorization N hNconn hNunipotent
            tG htSemi htNorm
        obtain ⟨m, hm, z, hz, hnN⟩ := hdecomp nN
        obtain ⟨vN, rfl⟩ := hm
        let vG := N.inclusion.onPoints vN
        let zG := N.inclusion.onPoints z
        have hvG : vG ∈ N.toSubgroup := (N.pointEquiv vN).property
        have hzG : zG ∈ N.toSubgroup := (N.pointEquiv z).property
        have hnAmbient : nG = semisimpleCommutator tG vG * zG := by
          have h := congrArg N.inclusion.onPoints hnN
          rw [map_mul, semisimpleCommutatorOn_inclusion] at h
          exact hnN_apply.symm.trans h
        have hzCommT : zG * tG = tG * zG := by
          apply (semisimpleCommutator_eq_one_iff_commute tG zG).mp
          have h := congrArg N.inclusion.onPoints hz
          rw [semisimpleCommutatorOn_inclusion,
            N.inclusion.onPoints.map_one] at h
          exact h
        have hzCommV : zG * vG = vG * zG :=
          hNcentral zG hzG vG (hNU hvG)
        have hzCommVInv : zG * vG⁻¹ = vG⁻¹ * zG := by
          exact (show Commute zG vG from hzCommV).inv_right.eq
        have hConjCommZ :
            (vG * tG * vG⁻¹) * zG = zG * (vG * tG * vG⁻¹) := by
          calc
            (vG * tG * vG⁻¹) * zG =
                vG * tG * (zG * vG⁻¹) := by rw [hzCommVInv]; group
            _ = vG * (zG * tG) * vG⁻¹ := by rw [hzCommT]; group
            _ = (vG * zG) * tG * vG⁻¹ := by group
            _ = zG * (vG * tG * vG⁻¹) := by rw [← hzCommV]; group
        have hs₁Jordan : s₁ = (vG * tG * vG⁻¹) * zG := by
          rw [hs₁eq, hnAmbient]
          simp only [semisimpleCommutator]
          calc
            vG * tG * vG⁻¹ * tG⁻¹ * zG * tG =
                vG * tG * vG⁻¹ * tG⁻¹ * (zG * tG) := by group
            _ = vG * tG * vG⁻¹ * tG⁻¹ * (tG * zG) := by rw [hzCommT]
            _ = vG * tG * vG⁻¹ * zG := by group
        have hzUni : IsUnipotentElement G zG := by
          let zN := z
          exact morphism_preserves_unipotentElement N.inclusion zN (hNunipotent zN)
        have hvSemi : IsSemisimpleElement G (vG * tG * vG⁻¹) :=
          semisimpleElement_conjugate_local htSemi
        let jd : JordanDecomposition s₁ :=
          { semisimplePart := vG * tG * vG⁻¹
            unipotentPart := zG
            eq_mul := hs₁Jordan
            commute := hConjCommZ
            semisimple := hvSemi
            unipotent := hzUni }
        let trivial : JordanDecomposition s₁ :=
          { semisimplePart := s₁
            unipotentPart := 1
            eq_mul := by simp
            commute := Commute.one_right _
            semisimple := hs₁Semi
            unipotent := one_isUnipotentElement G }
        have hzOne : zG = 1 :=
          congrArg JordanDecomposition.unipotentPart (jd.unique trivial)
        have hvConj : vG⁻¹ * s₁ * vG = tG := by
          rw [hs₁Jordan, hzOne]
          group
        let w := uG * vG
        have hvU : vG ∈ U.toSubgroup := hNU hvG
        have hwU : w ∈ U.toSubgroup := U.toSubgroup.mul_mem huG hvU
        refine ⟨w, hwU, ?_⟩
        rw [show w⁻¹ * s * w = vG⁻¹ * s₁ * vG by simp [w, s₁]; group]
        rw [hvConj]
        exact htG

end Theory.AlgebraicGroup
