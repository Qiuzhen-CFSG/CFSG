module

public import Theory.AlgebraicGroup.Solvable.Triangular
public import Theory.AlgebraicGroup.Jordan.Commutative
public import Theory.AlgebraicGroup.Unipotent.SemisimpleCommutator
public import Theory.AlgebraicGroup.Product

/-!
# Nilpotent connected solvable algebraic groups

This module proves the structural part of Borel, *Linear Algebraic Groups*, Chapter 3,
Theorem 10.6(3). For a connected solvable algebraic group whose point group is nilpotent,
every semisimple point is central. The semisimple points form a closed connected subtorus
`S`, the unipotent points form the connected unipotent radical `U`, and multiplication
gives the internal direct-product data: `S ∩ U = 1` and every point factors as `s * u`.
The converse-facing corollary supplies a noncentral semisimple point whenever the connected
solvable point group is not nilpotent.

The proof follows Borel 10.6(3). Proposition 9.3(3) makes the semisimple commutator image
inside `U` invariant under the same commutator map; nilpotence forces that image into every
lower-central term and hence makes it trivial. Borel 4.7 then supplies the closed semisimple
locus in the center. Connectedness of this factor is obtained by comparing it with its
identity component: its product with `U` is a closed finite-index subgroup, hence is all of
the connected ambient group, and semisimple-unipotent uniqueness removes the residual
finite component. The nonnilpotent witness is proved contrapositively from the triangular
unipotent radical and nilpotence of the quotient by the center.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open scoped commutatorElement IsMulCommutative
open scoped Pointwise

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma mem_invtSubmodule_iff_of_inverse_local
    {M : Type*} [AddCommGroup M] [Module k M]
    {T S : Module.End k M} (hTS : T.comp S = 1) (hST : S.comp T = 1)
    (P : Submodule k M) [Module.Finite k P] :
    P ∈ T.invtSubmodule ↔ P ∈ S.invtSubmodule := by
  have forward {A B : Module.End k M} (hBA : B.comp A = 1)
      (hPA : P ∈ A.invtSubmodule) : P ∈ B.invtSubmodule := by
    let AP : Module.End k P := A.restrict hPA
    have hAinj : Function.Injective A := by
      intro x y hxy
      calc
        x = B (A x) := by
          have hx := LinearMap.congr_fun hBA x
          simpa using hx.symm
        _ = B (A y) := congrArg B hxy
        _ = y := by
          have hy := LinearMap.congr_fun hBA y
          simpa using hy
    have hAPinj : Function.Injective AP := by
      intro x y hxy
      apply Subtype.ext
      apply hAinj
      exact congrArg Subtype.val hxy
    have hAPsurj : Function.Surjective AP :=
      LinearMap.surjective_of_injective hAPinj
    intro x hx
    rcases hAPsurj ⟨x, hx⟩ with ⟨y, hy⟩
    have hAy : A y.1 = x := congrArg Subtype.val hy
    have hBx : B x = y.1 := by
      calc
        B x = B (A y.1) := by rw [hAy]
        _ = y.1 := by
          have hy' := LinearMap.congr_fun hBA y.1
          simpa using hy'
    change B x ∈ P
    rw [hBx]
    exact y.2
  exact ⟨forward hST, forward hTS⟩

omit [IsAlgClosed k] in
private lemma finitelySemisimple_of_inverse_local
    {M : Type*} [AddCommGroup M] [Module k M]
    {T S : Module.End k M} (hT : T.IsFinitelySemisimple)
    (hTS : T.comp S = 1) (hST : S.comp T = 1) :
    S.IsFinitelySemisimple := by
  intro P hPS hPfinite
  let : Module.Finite k P := hPfinite
  have hPT : P ∈ T.invtSubmodule :=
    (mem_invtSubmodule_iff_of_inverse_local hTS hST P).mpr hPS
  let TP : Module.End k P := T.restrict hPT
  let SP : Module.End k P := S.restrict hPS
  have hTPSP : TP.comp SP = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hTS x.1
  have hSPTP : SP.comp TP = 1 := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun hST x.1
  have hinv : ∀ Q : Submodule k P,
      Q ∈ TP.invtSubmodule ↔ Q ∈ SP.invtSubmodule :=
    fun Q => mem_invtSubmodule_iff_of_inverse_local hTPSP hSPTP Q
  have hTPsem : TP.IsSemisimple := hT P hPT hPfinite
  rw [Module.End.isSemisimple_iff] at hTPsem ⊢
  intro Q hQS
  obtain ⟨R, hRT, hcompl⟩ := hTPsem Q ((hinv Q).mpr hQS)
  exact ⟨R, (hinv R).mp hRT, hcompl⟩

omit [IsAlgClosed k] in
private lemma semisimpleElement_inv_local
    {G : Variety k} [AlgebraicGroup G] {x : Variety.Point G}
    (hx : IsSemisimpleElement G x) :
    IsSemisimpleElement G x⁻¹ := by
  change Module.End.IsFinitelySemisimple (rightTranslationPullback G x⁻¹)
  apply finitelySemisimple_of_inverse_local
    (T := rightTranslationPullback G x)
    (S := rightTranslationPullback G x⁻¹)
  · exact hx
  · exact rightTranslationPullback_comp_inv G x
  · exact rightTranslationPullback_inv_comp G x

private lemma semisimpleElement_mul_of_commute_local
    {G : Variety k} [AlgebraicGroup G] {x y : Variety.Point G}
    (hx : IsSemisimpleElement G x) (hy : IsSemisimpleElement G y)
    (hxy : Commute x y) : IsSemisimpleElement G (x * y) := by
  have hTU : Commute (rightTranslationPullback G x)
      (rightTranslationPullback G y) := by
    change (rightTranslationPullback G x).comp (rightTranslationPullback G y) =
      (rightTranslationPullback G y).comp (rightTranslationPullback G x)
    rw [← rightTranslationPullback_mul, ← rightTranslationPullback_mul]
    exact congrArg (rightTranslationPullback G) hxy.eq
  rw [IsSemisimpleElement, rightTranslationPullback_mul]
  exact Module.End.IsFinitelySemisimple.mul_of_commute
    (rightTranslationPullback_locallyFinite G x)
    (rightTranslationPullback_locallyFinite G y) hx hy hTU

private lemma commutator_le_unipotentRadical_local
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (U : ClosedSubgroup G)
    (hU : IsUnipotentRadicalSubgroup U) :
    commutator (Variety.Point G) ≤ U.toSubgroup := by
  obtain ⟨n, hn, H, ⟨e⟩⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
      hsolvable hconnected
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let P : TriangularPresentation G :=
    { n := n, positive := hn, subgroup := H, iso := e }
  have hP : P.unipotentRadical = U := by
    apply SetLike.coe_injective
    ext x
    exact (P.mem_unipotentRadical_iff_characteristicFree x).trans
      (hU x).symm
  rw [← hP]
  exact (P.commutator_le_kernelIdentityComponent hconnected).trans
    P.kernelIdentityComponent_le_unipotentRadical

private lemma commutatorImage_mem_lowerCentralSeries_local
    {G : Variety k} [AlgebraicGroup G]
    (U : ClosedSubgroup G) (hUconn : Variety.IsConnected U.carrierVariety)
    (hU : IsUnipotentAlgebraicGroup U.carrierVariety)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s)
    (hsNorm : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)))
    (n : ℕ) :
    ∀ x, x ∈ semisimpleCommutatorImage U s hsNorm →
      U.inclusion.onPoints x ∈
        Subgroup.lowerCentralSeries (⊤ : Subgroup (Variety.Point G)) n := by
  induction n with
  | zero =>
      intro x hx
      trivial
  | succ n ih =>
      intro x hx
      rw [Subgroup.lowerCentralSeries_succ]
      rw [← semisimpleCommutator_image_image_eq U hUconn hU s hsSemi hsNorm] at hx
      rcases hx with ⟨y, hy, rfl⟩
      rw [semisimpleCommutatorOn_inclusion,
        semisimpleCommutator_eq_commutator]
      apply Subgroup.commutator_mem_commutator
      · exact ih y hy
      · exact Subgroup.mem_top _

omit [IsAlgClosed k] in
private lemma semisimpleCommutator_eq_one_iff_commute_local
    {G : Variety k} [AlgebraicGroup G] (s u : Variety.Point G) :
    semisimpleCommutator s u = 1 ↔ u * s = s * u := by
  simp only [semisimpleCommutator]
  constructor
  · intro h
    calc
      u * s = (u * s * u⁻¹ * s⁻¹) * (s * u) := by group
      _ = s * u := by rw [h, one_mul]
  · intro h
    rw [h]
    group

private lemma semisimple_centralizes_unipotentRadical_local
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (hnilpotent : Group.IsNilpotent (Variety.Point G))
    (U : ClosedSubgroup G) (hU : IsUnipotentRadicalSubgroup U)
    (s : Variety.Point G) (hsSemi : IsSemisimpleElement G s) :
    ∀ u : Variety.Point G, u ∈ U.toSubgroup → u * s = s * u := by
  have hUnormal := hU.normal_of_solvable_connected hsolvable hconnected
  have hUnconn := hU.isConnected_of_solvable_connected hsolvable hconnected
  have hUuni := hU.isUnipotent_of_solvable_connected hsolvable hconnected
  have hsNorm : s ∈ Subgroup.normalizer (U.toSubgroup : Set (Variety.Point G)) := by
    have htop : Subgroup.normalizer
        (U.toSubgroup : Set (Variety.Point G)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hUnormal
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnilpotent
  intro u hu
  let uU : Variety.Point U.carrierVariety := U.pointEquiv.symm ⟨u, hu⟩
  let d : Variety.Point U.carrierVariety :=
    semisimpleCommutatorOn U s hsNorm uU
  have hdimage : d ∈ semisimpleCommutatorImage U s hsNorm := ⟨uU, rfl⟩
  have hdlower := commutatorImage_mem_lowerCentralSeries_local U hUnconn hUuni
      s hsSemi hsNorm n d hdimage
  rw [hn] at hdlower
  have hdone : U.inclusion.onPoints d = 1 := by
    exact Subgroup.mem_bot.mp hdlower
  apply (semisimpleCommutator_eq_one_iff_commute_local s u).mp
  calc
    semisimpleCommutator s u =
        semisimpleCommutator s (U.inclusion.onPoints uU) := by
          have huU : U.inclusion.onPoints uU = u := by
            change (U.pointEquiv uU).val = u
            rw [U.pointEquiv.apply_symm_apply]
          rw [huU]
    _ = U.inclusion.onPoints d :=
      (semisimpleCommutatorOn_inclusion U s hsNorm uU).symm
    _ = 1 := hdone

/-- Every semisimple point of a connected nilpotent solvable algebraic group
is central. -/
public theorem semisimpleElement_mem_center_of_isNilpotent_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (hnilpotent : Group.IsNilpotent (Variety.Point G))
    {s : Variety.Point G} (hs : IsSemisimpleElement G s) :
    s ∈ Subgroup.center (Variety.Point G) := by
  obtain ⟨U, hU⟩ := exists_unipotentRadicalSubgroup_of_solvable_connected
    hsolvable hconnected
  have hsU := semisimple_centralizes_unipotentRadical_local
    hsolvable hconnected hnilpotent U hU s hs
  have hDU : commutator (Variety.Point G) ≤ U.toSubgroup :=
    commutator_le_unipotentRadical_local hsolvable hconnected U hU
  let C : Subgroup (Variety.Point G) := Subgroup.centralizer ({s} : Set _)
  have hsC : s ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    simp only [Set.mem_singleton_iff.mp hx]
  have hUC : U.toSubgroup ≤ C := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    simpa only [Set.mem_singleton_iff.mp hx] using (hsU u hu).symm
  have hDC : commutator (Variety.Point G) ≤ C := hDU.trans hUC
  have hCnormal : C.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact (Subgroup.commutator_mono le_top le_rfl).trans hDC
  rw [Subgroup.mem_center_iff]
  intro g
  have hconjC : g * s * g⁻¹ ∈ C := hCnormal.conj_mem s hsC g
  have hconjComm : Commute (g * s * g⁻¹) s := by
    exact (Subgroup.mem_centralizer_iff.mp hconjC s (Set.mem_singleton s)).symm
  let c : AlgebraicGroup.Morphism G G :=
    { toVariety := conjugationByMorphism G g
      map_one := by simp [conjugationByMorphism_apply]
      map_mul := by
        intro x y
        simp only [conjugationByMorphism_apply]
        group }
  have hconjSemi : IsSemisimpleElement G (g * s * g⁻¹) := by
    have hc := morphism_preserves_semisimpleElement c s hs
    change IsSemisimpleElement G ((conjugationByMorphism G g).toFun s) at hc
    rw [conjugationByMorphism_apply] at hc
    exact hc
  have hsinvSemi : IsSemisimpleElement G s⁻¹ :=
    semisimpleElement_inv_local hs
  have hdSemi : IsSemisimpleElement G (g * s * g⁻¹ * s⁻¹) :=
    semisimpleElement_mul_of_commute_local hconjSemi hsinvSemi hconjComm.inv_right
  have hdU : g * s * g⁻¹ * s⁻¹ ∈ U.toSubgroup := by
    apply hDU
    exact Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤)
      (Subgroup.mem_top _) (Subgroup.mem_top _)
  have hdUni : IsUnipotentElement G (g * s * g⁻¹ * s⁻¹) :=
    (hU _).mp hdU
  have hdOne : g * s * g⁻¹ * s⁻¹ = 1 :=
    semisimple_unipotent_eq_one _ hdSemi hdUni
  exact (semisimpleCommutator_eq_one_iff_commute_local s g).mp hdOne

/-- In the nilpotent connected solvable case, the semisimple points form a
closed central subgroup and multiply with the unipotent radical onto the
whole group. -/
public theorem exists_closed_semisimple_factor_of_isNilpotent_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (hnilpotent : Group.IsNilpotent (Variety.Point G)) :
    ∃ U : ClosedSubgroup G, IsUnipotentRadicalSubgroup U ∧
      ∃ S : ClosedSubgroup G,
        (∀ x : Variety.Point G, x ∈ S ↔ IsSemisimpleElement G x) ∧
        S.toSubgroup ≤ Subgroup.center (Variety.Point G) ∧
        (∀ x : Variety.Point G, ∃ s u,
          s ∈ S.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = s * u) := by
  obtain ⟨U, hU⟩ := exists_unipotentRadicalSubgroup_of_solvable_connected
    hsolvable hconnected
  let Z : ClosedSubgroup G := (ClosedSubgroup.top (G := G)).centralizer
  let hZcarrier : Z.toSubgroup = Subgroup.center (Variety.Point G) := by
    apply SetLike.coe_injective
    ext x
    change x ∈ Subgroup.centralizer (Set.univ : Set (Variety.Point G)) ↔
      x ∈ Subgroup.center (Variety.Point G)
    constructor
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro g
      exact (Subgroup.mem_centralizer_iff.mp hx g (Set.mem_univ g))
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro g _
      exact Subgroup.mem_center_iff.mp hx g
  have hZcomm : IsMulCommutative (Variety.Point Z.carrierVariety) := by
    apply IsMulCommutative.of_comm
    intro x y
    apply Z.inclusion_injective
    have hx : Z.inclusion.onPoints x ∈
        Subgroup.center (Variety.Point G) := by
      rw [← hZcarrier]
      exact (Z.pointEquiv x).property
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hx _).symm
  letI : AlgebraicGroup Z.carrierVariety := Z.carrierAlgebraicGroup
  let S₀ : ClosedSubgroup Z.carrierVariety :=
    commutativeSemisimpleSubgroup Z.carrierVariety hZcomm
  letI : AlgebraicGroup S₀.carrierVariety := S₀.carrierAlgebraicGroup
  let f : AlgebraicGroup.Morphism S₀.carrierVariety G :=
    Z.inclusion.comp S₀.inclusion
  let S : ClosedSubgroup G := f.imageClosedSubgroup
  have hSemiff : ∀ x : Variety.Point G,
      x ∈ S.toSubgroup ↔ IsSemisimpleElement G x := by
    intro x
    constructor
    · intro hx
      change x ∈ f.image at hx
      rcases hx with ⟨z, rfl⟩
      have hzZsemi : IsSemisimpleElement Z.carrierVariety
          (S₀.inclusion.onPoints z) :=
        (mem_commutativeSemisimpleSubgroup_iff Z.carrierVariety hZcomm _).mp
          (S₀.pointEquiv z).property
      have hzSsemi : IsSemisimpleElement S₀.carrierVariety z :=
        (closedSubgroup_semisimpleElement_iff S₀
          (S₀.pointEquiv z).property).mp hzZsemi
      exact morphism_preserves_semisimpleElement f z
        hzSsemi
    · intro hx
      have hxcenter : x ∈ Subgroup.center (Variety.Point G) :=
        semisimpleElement_mem_center_of_isNilpotent_of_solvable_connected
          hsolvable hconnected hnilpotent hx
      have hxZ : x ∈ Z.toSubgroup := by
        rw [hZcarrier]
        exact hxcenter
      let z : Variety.Point Z.carrierVariety := Z.pointEquiv.symm ⟨x, hxZ⟩
      have hz : IsSemisimpleElement Z.carrierVariety z := by
        apply (closedSubgroup_semisimpleElement_iff Z hxZ).mp hx
      have hzS : z ∈ S₀.toSubgroup :=
        (mem_commutativeSemisimpleSubgroup_iff Z.carrierVariety hZcomm z).mpr hz
      let zs : Variety.Point S₀.carrierVariety := S₀.pointEquiv.symm ⟨z, hzS⟩
      change x ∈ f.image
      refine ⟨zs, ?_⟩
      change Z.inclusion.onPoints (S₀.inclusion.onPoints zs) = x
      have hzs : S₀.inclusion.onPoints zs = z := by
        change (S₀.pointEquiv zs).val = z
        rw [S₀.pointEquiv.apply_symm_apply]
      rw [hzs]
      change (Z.pointEquiv (Z.pointEquiv.symm ⟨x, hxZ⟩)).val = x
      rw [Z.pointEquiv.apply_symm_apply]
  refine ⟨U, hU, S, hSemiff, ?_, ?_⟩
  · intro x hx
    exact semisimpleElement_mem_center_of_isNilpotent_of_solvable_connected
      hsolvable hconnected hnilpotent
      ((hSemiff x).mp hx)
  · intro x
    let d := jordanDecomposition x
    have hds : d.semisimplePart ∈ S.toSubgroup :=
      (hSemiff _).mpr d.semisimple
    have hdu : d.unipotentPart ∈ U.toSubgroup :=
      (hU _).mpr d.unipotent
    exact ⟨d.semisimplePart, d.unipotentPart, hds, hdu, d.eq_mul⟩

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

private lemma semisimpleFactor_isConnected_local
    {G : Variety k} [AlgebraicGroup G]
    (hconnected : Variety.IsConnected G)
    (U S : ClosedSubgroup G)
    (hUnormal : U.toSubgroup.Normal)
    (hU : IsUnipotentRadicalSubgroup U)
    (hScenter : S.toSubgroup ≤ Subgroup.center (Variety.Point G))
    (hSemiff : ∀ x : Variety.Point G,
      x ∈ S.toSubgroup ↔ IsSemisimpleElement G x)
    (hdecomp : ∀ x : Variety.Point G, ∃ s u,
      s ∈ S.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = s * u) :
    Variety.IsConnected S.carrierVariety := by
  let S₀ : ClosedSubgroup G := S.identityComponentAmbient
  let K : Subgroup (Variety.Point G) := S₀.toSubgroup
  have hS₀S : K ≤ S.toSubgroup := S.identityComponentAmbient_le
  have hKcenter : K ≤ Subgroup.center (Variety.Point G) := hS₀S.trans hScenter
  letI : K.Normal := by
    refine ⟨fun a ha b => ?_⟩
    have hac := Subgroup.mem_center_iff.mp (hKcenter ha) b
    rw [hac]
    simpa using ha
  letI : U.toSubgroup.Normal := hUnormal
  letI : AlgebraicGroup
      (Variety.prod S₀.carrierVariety U.carrierVariety) :=
    AlgebraicGroup.prod S₀.carrierVariety U.carrierVariety
  let left : AlgebraicGroup.Morphism
      (Variety.prod S₀.carrierVariety U.carrierVariety) G :=
    S₀.inclusion.comp (AlgebraicGroup.Morphism.fst S₀.carrierVariety U.carrierVariety)
  let right : AlgebraicGroup.Morphism
      (Variety.prod S₀.carrierVariety U.carrierVariety) G :=
    U.inclusion.comp (AlgebraicGroup.Morphism.snd S₀.carrierVariety U.carrierVariety)
  let pair := AlgebraicGroup.Morphism.prod left right
  let m : AlgebraicGroup.Morphism
      (Variety.prod S₀.carrierVariety U.carrierVariety) G := {
    toVariety := (AlgebraicGroup.mulMorphism G).comp pair.toVariety
    map_one := by
        change (Variety.prodPointEquiv G G (pair.toVariety.toFun 1)).1 *
            (Variety.prodPointEquiv G G (pair.toVariety.toFun 1)).2 = 1
        have hp : pair.toVariety.toFun 1 =
            (1 : Variety.Point (Variety.prod G G)) := pair.map_one
        rw [hp]
        have hone : Variety.prodPointEquiv G G
            (1 : Variety.Point (Variety.prod G G)) = (1, 1) := by
          apply Prod.ext <;> rfl
        rw [hone]
        exact mul_one 1
    map_mul := by
        intro x y
        let px := Variety.prodPointEquiv S₀.carrierVariety U.carrierVariety x
        let py := Variety.prodPointEquiv S₀.carrierVariety U.carrierVariety y
        have hpairx : Variety.prodPointEquiv G G (pair.toVariety.toFun x) =
            (left.onPoints x, right.onPoints x) := by
          rfl
        have hpairy : Variety.prodPointEquiv G G (pair.toVariety.toFun y) =
            (left.onPoints y, right.onPoints y) := by
          rfl
        have hyK : S₀.inclusion.onPoints py.1 ∈ K :=
          (S₀.pointEquiv py.1).property
        have hc : Commute (right.onPoints x) (left.onPoints y) := by
          change Commute (U.inclusion.onPoints px.2)
            (S₀.inclusion.onPoints py.1)
          exact Subgroup.mem_center_iff.mp (hKcenter hyK)
            (U.inclusion.onPoints px.2)
        change (Variety.prodPointEquiv G G (pair.toVariety.toFun (x * y))).1 *
            (Variety.prodPointEquiv G G (pair.toVariety.toFun (x * y))).2 =
          ((Variety.prodPointEquiv G G (pair.toVariety.toFun x)).1 *
            (Variety.prodPointEquiv G G (pair.toVariety.toFun x)).2) *
          ((Variety.prodPointEquiv G G (pair.toVariety.toFun y)).1 *
            (Variety.prodPointEquiv G G (pair.toVariety.toFun y)).2)
        have hpm : pair.toVariety.toFun (x * y) =
            pair.toVariety.toFun x * pair.toVariety.toFun y := pair.map_mul x y
        rw [hpm, Variety.prodPointEquiv_mul, hpairx, hpairy]
        change (left.onPoints x * left.onPoints y) *
            (right.onPoints x * right.onPoints y) =
          (left.onPoints x * right.onPoints x) *
            (left.onPoints y * right.onPoints y)
        calc
          _ = left.onPoints x *
              (left.onPoints y * right.onPoints x) *
                right.onPoints y := by group
          _ = left.onPoints x *
              (right.onPoints x * left.onPoints y) *
                right.onPoints y := by rw [hc.eq]
          _ = _ := by group }
  let H : ClosedSubgroup G := m.imageClosedSubgroup
  have hm (z : Variety.Point
      (Variety.prod S₀.carrierVariety U.carrierVariety)) :
      m.onPoints z =
        S₀.inclusion.onPoints
            (Variety.prodPointEquiv S₀.carrierVariety U.carrierVariety z).1 *
          U.inclusion.onPoints
            (Variety.prodPointEquiv S₀.carrierVariety U.carrierVariety z).2 := by
    rfl
  have hHset : (H.toSubgroup : Set (Variety.Point G)) =
      (K : Set (Variety.Point G)) * (U.toSubgroup : Set (Variety.Point G)) := by
    ext x
    constructor
    · intro hx
      change x ∈ m.image at hx
      rcases hx with ⟨z, rfl⟩
      refine Set.mem_mul.mpr ⟨S₀.inclusion.onPoints
          (Variety.prodPointEquiv _ _ z).1,
        (S₀.pointEquiv _).property,
        U.inclusion.onPoints (Variety.prodPointEquiv _ _ z).2,
        (U.pointEquiv _).property, ?_⟩
      exact (hm z).symm
    · intro hx
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx
      let a' : Variety.Point S₀.carrierVariety := S₀.pointEquiv.symm ⟨a, ha⟩
      let b' : Variety.Point U.carrierVariety := U.pointEquiv.symm ⟨b, hb⟩
      let z := (Variety.prodPointEquiv S₀.carrierVariety U.carrierVariety).symm (a', b')
      refine ⟨z, ?_⟩
      rw [hm, Equiv.apply_symm_apply]
      have haa : S₀.inclusion.onPoints a' = a := by
        change (S₀.pointEquiv a').val = a
        rw [S₀.pointEquiv.apply_symm_apply]
      have hbb : U.inclusion.onPoints b' = b := by
        change (U.pointEquiv b').val = b
        rw [U.pointEquiv.apply_symm_apply]
      rw [haa, hbb, hab]
  have hHeq : H.toSubgroup = K ⊔ U.toSubgroup := by
    apply SetLike.coe_injective
    rw [hHset, Subgroup.mul_normal]
  have hHnormal : H.toSubgroup.Normal := by
    rw [hHeq]
    exact Subgroup.sup_normal K U.toSubgroup
  have hKleH : K ≤ H.toSubgroup := by
    rw [hHeq]
    intro x hx
    exact Subgroup.mem_sup_left hx
  have hUleH : U.toSubgroup ≤ H.toSubgroup := by
    rw [hHeq]
    intro x hx
    exact Subgroup.mem_sup_right hx
  let I : Subgroup (Variety.Point S.carrierVariety) :=
    AlgebraicGroup.identityComponentSubgroup S.carrierVariety
  have hI_normal : I.Normal := by
    change (AlgebraicGroup.identityComponentClosedSubgroup
      S.carrierVariety).toSubgroup.Normal
    exact AlgebraicGroup.identityComponentClosedSubgroup_isNormal
      S.carrierVariety
  let inc : Variety.Point S.carrierVariety →* Variety.Point G :=
    S.inclusion.onPoints
  have hIcomap : I ≤ Subgroup.comap inc H.toSubgroup := by
    intro z hz
    apply hKleH
    apply (ClosedSubgroup.mem_identityComponentAmbient_iff S
      (S.inclusion.onPoints z)).mpr
    refine ⟨z, hz, rfl⟩
  let qmap := QuotientGroup.map I H.toSubgroup inc hIcomap
  have hqsurj : Function.Surjective qmap := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H.toSubgroup y
    obtain ⟨s, u, hs, hu, hgu⟩ := hdecomp g
    let ss : Variety.Point S.carrierVariety :=
      S.pointEquiv.symm ⟨s, hs⟩
    refine ⟨QuotientGroup.mk' I ss, ?_⟩
    · rw [QuotientGroup.map_mk']
      change QuotientGroup.mk' H.toSubgroup s = QuotientGroup.mk' H.toSubgroup g
      rw [hgu]
      exact (QuotientGroup.mk'_eq_mk' H.toSubgroup).mpr
        ⟨u, hUleH hu, rfl⟩
  letI : Finite (Variety.Point S.carrierVariety ⧸ I) := by
    simpa [I] using finite_quotient_identityComponentSubgroup S.carrierVariety
  letI : Finite (Variety.Point G ⧸ H.toSubgroup) :=
    Finite.of_surjective qmap hqsurj
  letI : H.toSubgroup.FiniteIndex :=
    H.toSubgroup.finiteIndex_of_finite_quotient
  have htop_sub : (⊤ : Subgroup (Variety.Point G)) ≤ H.toSubgroup := by
    have hcomponent := identityComponent_subset_of_finiteIndexSubgroup G H
    have htopid : AlgebraicGroup.identityComponent G = Set.univ :=
      (identityComponent_eq_univ_iff_isConnected G).mpr hconnected
    intro x hx
    apply hcomponent
    rw [htopid]
    trivial
  have hSleS₀ : S.toSubgroup ≤ K := by
    intro s hs
    have hsmul := htop_sub (Subgroup.mem_top s)
    have hsmul' : s ∈ (K : Set (Variety.Point G)) *
        (U.toSubgroup : Set (Variety.Point G)) := by
      rw [← hHset]
      exact hsmul
    obtain ⟨a, ha, u, hu, hau⟩ := Set.mem_mul.mp hsmul'
    have haS : a ∈ S.toSubgroup := hS₀S ha
    have huS : u ∈ S.toSubgroup := by
      have has : a⁻¹ * s ∈ S.toSubgroup :=
        S.toSubgroup.mul_mem (S.toSubgroup.inv_mem haS) hs
      rw [← hau] at has
      simpa [mul_assoc] using has
    have htriv : u = 1 := by
      have hsemi : IsSemisimpleElement G u := (hSemiff _).mp huS
      have huni : IsUnipotentElement G u := (hU _).mp hu
      have := semisimple_unipotent_eq_one _ hsemi huni
      exact this
    have hsa : s = a := by
      simpa [htriv] using hau.symm
    simpa [hsa] using ha
  have hSeq : S = S₀ := by
    apply SetLike.coe_injective
    exact Set.Subset.antisymm hSleS₀ hS₀S
  have hS0ambient : _root_.IsConnected
      (S₀ : Set (Variety.Point G)) := by
    change _root_.IsConnected
      (S.identityComponentAmbient : Set (Variety.Point G))
    exact S.identityComponentAmbient_isConnected
  have hSambient : _root_.IsConnected
      (S : Set (Variety.Point G)) := by
    rw [hSeq]
    exact hS0ambient
  exact closedSubgroup_carrier_isConnected_local S hSambient

/-- The internal direct-product form of Borel 10.6(3): the connected
unipotent radical has a central subtorus complement, with trivial intersection
and pointwise product equal to the ambient group. -/
public theorem exists_subtorus_complement_of_isNilpotent_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (hnilpotent : Group.IsNilpotent (Variety.Point G)) :
    ∃ U : ClosedSubgroup G, IsUnipotentRadicalSubgroup U ∧
      Variety.IsConnected U.carrierVariety ∧
      ∃ S : ClosedSubgroup G, IsSubtorus S ∧
        S.toSubgroup ≤ Subgroup.center (Variety.Point G) ∧
        S.toSubgroup ⊓ U.toSubgroup = ⊥ ∧
        (∀ x : Variety.Point G, ∃ s u,
          s ∈ S.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = s * u) := by
  obtain ⟨U, hU, S, hSemiff, hScenter, hdecomp⟩ :=
    exists_closed_semisimple_factor_of_isNilpotent_of_solvable_connected
      hsolvable hconnected hnilpotent
  have hUnormal : U.toSubgroup.Normal :=
    hU.normal_of_solvable_connected hsolvable hconnected
  have hUconnected : Variety.IsConnected U.carrierVariety :=
    hU.isConnected_of_solvable_connected hsolvable hconnected
  have hSconn : Variety.IsConnected S.carrierVariety :=
    semisimpleFactor_isConnected_local hconnected U S hUnormal hU hScenter
      hSemiff hdecomp
  have hScomm : IsMulCommutative (Variety.Point S.carrierVariety) := by
    apply IsMulCommutative.of_comm
    intro x y
    apply S.inclusion_injective
    have hx := hScenter (S.pointEquiv x).property
    rw [map_mul, map_mul]
    exact (Subgroup.mem_center_iff.mp hx (S.inclusion.onPoints y)).symm
  have hSsemi : ∀ z : Variety.Point S.carrierVariety,
      IsSemisimpleElement S.carrierVariety z := by
    intro z
    apply (closedSubgroup_semisimpleElement_iff S
      (S.pointEquiv z).property).mp
    exact (hSemiff _).mp (S.pointEquiv z).property
  have hStorus : IsSubtorus S :=
    isTorus_of_isConnected_isMulCommutative_all_semisimple
      hSconn hScomm hSsemi
  have hSinf : S.toSubgroup ⊓ U.toSubgroup = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxs : IsSemisimpleElement G x :=
        (hSemiff x).mp (Subgroup.mem_inf.mp hx).1
      have hxu : IsUnipotentElement G x :=
        (hU x).mp (Subgroup.mem_inf.mp hx).2
      exact Subgroup.mem_bot.mpr (semisimple_unipotent_eq_one _ hxs hxu)
    · exact bot_le
  exact ⟨U, hU, hUconnected, S, hStorus, hScenter, hSinf, hdecomp⟩

/-- A nonnilpotent connected solvable algebraic group contains a semisimple
point which is not central. -/
public theorem exists_noncentral_semisimpleElement_of_not_nilpotent
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (hnilpotent : ¬ Group.IsNilpotent (Variety.Point G)) :
    ∃ s : Variety.Point G,
      IsSemisimpleElement G s ∧
        s ∉ Subgroup.center (Variety.Point G) := by
  by_contra h
  push Not at h
  obtain ⟨n, hn, H, hIso⟩ :=
    exists_iso_closedSubgroup_tVariety_of_isSolvable_isConnected
      hsolvable hconnected
  letI : AlgebraicGroup H.carrierVariety := H.carrierAlgebraicGroup
  let P : TriangularPresentation G :=
    { n := n
      positive := hn
      subgroup := H
      iso := Classical.choice hIso }
  let U := P.unipotentRadical
  letI : AlgebraicGroup U.carrierVariety := U.carrierAlgebraicGroup
  have hU : IsUnipotentAlgebraicGroup U.carrierVariety := by
    intro x
    apply closedSubgroup_unipotent_of_ambient U (U.pointEquiv x).property
    exact (P.mem_unipotentRadical_iff_characteristicFree
      (U.inclusion.onPoints x)).mp (U.pointEquiv x).property
  letI : Group.IsNilpotent (Variety.Point U.carrierVariety) :=
    unipotentGroup_isNilpotent hU
  let q : Variety.Point G →*
      (Variety.Point G ⧸ Subgroup.center (Variety.Point G)) :=
    QuotientGroup.mk' (Subgroup.center (Variety.Point G))
  let f : Variety.Point U.carrierVariety →*
      (Variety.Point G ⧸ Subgroup.center (Variety.Point G)) :=
    q.comp U.inclusion.onPoints
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center (Variety.Point G)) y
    let d := jordanDecomposition g
    have hsCenter : d.semisimplePart ∈
        Subgroup.center (Variety.Point G) :=
      h d.semisimplePart d.semisimple
    have huU : d.unipotentPart ∈ U :=
      (P.mem_unipotentRadical_iff_characteristicFree d.unipotentPart).mpr
        d.unipotent
    let u : Variety.Point U.carrierVariety :=
      U.pointEquiv.symm ⟨d.unipotentPart, huU⟩
    refine ⟨u, ?_⟩
    have hu : U.inclusion.onPoints u = d.unipotentPart := by
      change (U.pointEquiv u).val = d.unipotentPart
      simp [u]
    have hsOne : q d.semisimplePart = 1 :=
      (QuotientGroup.eq_one_iff d.semisimplePart).mpr hsCenter
    change q (U.inclusion.onPoints u) = q g
    calc
      q (U.inclusion.onPoints u) = q d.unipotentPart := congrArg q hu
      _ = 1 * q d.unipotentPart := (one_mul _).symm
      _ = q d.semisimplePart * q d.unipotentPart := by rw [hsOne]
      _ = q (d.semisimplePart * d.unipotentPart) :=
        (q.map_mul d.semisimplePart d.unipotentPart).symm
      _ = q g := congrArg q d.eq_mul.symm
  exact hnilpotent (Group.of_quotient_center_nilpotent
    (Group.nilpotent_of_surjective f hf))

end Theory.AlgebraicGroup
