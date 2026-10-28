module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationPrimeLift
public import Theory.GroupTheory.LocalSolvableCoreNormalizerImage
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.CoreShapes.PrimaryShapes.FixedInvolution
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualOddCoreNormalizerCover
public import Theory.GroupTheory.Fitting.PrimeSubgroups
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.SylowSubgroupNormalizerImage
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Recognition of the original Cartan normalizer residual image

Let N = N_G(V₁), let J be the chosen normal C-component of N, and let
I be its literal image in N/O₂(N). In the noncentral Fitting branch,
I/F(I) is SL₂(p), p > 3. The solvable radical is the preimage of its
center. Its intersection with the specified Sylow subgroup is generated
by an involution t outside F(I). The primary fixed-subgroup theorems
make C_{F(I)}(t) cyclic; the perfect-cover theorem then identifies
N_I(⟨t⟩)^∞ with SL₂(p).

Solvable-kernel and subgroup transports identify this residual with the
actual image of K₀ = N_J(T ∩ O_{2,2′,2}(J))^∞ in N/O₂(N), retaining
the original Sylow and quotient maps. This discharges the recognition
premise of SourceOldResidualCartanNormalizationPrimeLift.

Source: Aschbacher--Smith, Proposition 9.3.1, printed p.732 of the
combined manuscript of 1 March 2004; the local structure input is A.3.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

theorem fixed_centralizer_isCyclic
    {𝒦 : GroupClass} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : PrimeSL2FittingQuotient L)
    (t : L) (ht : t ^ 2 = 1) (hnt : t ∉ fittingSubgroup L) :
    IsCyclic (fittingSubgroup L ⊓ centralizer ({t} : Set L) : Subgroup L) := by
  let C := fittingSubgroup L ⊓ centralizer ({t} : Set L)
  let : Group.IsNilpotent C := Subgroup.isNilpotent_of_ker_le_center
    (inclusion (show C ≤ fittingSubgroup L from inf_le_left))
    (by
      intro x hx
      have he : x = 1 := (inclusion_injective (show C ≤ fittingSubgroup L from inf_le_left)) hx
      rw [he]
      exact one_mem _)
  let : IsZGroup C := ⟨fun p hp S => by
    let : Fact p.Prime := ⟨hp⟩
    let P := (S : Subgroup C).map C.subtype
    have hPF : P ≤ fittingSubgroup L := (map_subtype_le _).trans inf_le_left
    have hPc : P ≤ centralizer ({t} : Set L) := (map_subtype_le _).trans inf_le_right
    have hP : IsPGroup p P := S.isPGroup'.map C.subtype
    have hcore : P ≤ pCore p L := hP.le_pCore_of_le_fitting hPF
    by_cases hd : p ∣ Nat.card (fittingSubgroup L)
    · let : IsCyclic (MulAut.conjNormal t : MulAut (pCore p L)).fixedSubgroup :=
        CoreShapes.PrimaryShapes.primary_fixedSubgroup_isCyclic hG hO hL hquot t ht hnt p hd
      let f : P →* (MulAut.conjNormal t : MulAut (pCore p L)).fixedSubgroup :=
        { toFun := fun x => ⟨⟨x,hcore x.property⟩, by
            rw [MulAut.mem_fixedSubgroup]
            apply Subtype.ext
            change t * (x : L) * t⁻¹ = x
            rw [hPc x.property t (by simp), mul_inv_cancel_right]⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      let : IsCyclic P := isCyclic_of_injective f (fun x y h => Subtype.ext
        (congrArg (fun z : (MulAut.conjNormal t : MulAut (pCore p L)).fixedSubgroup => ((z : pCore p L) : L)) h))
      exact isCyclic_of_injective (C.subtype.subgroupMap (S : Subgroup C))
        (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : P => (z : L)) h)))
    · have hbot : P = ⊥ := by
        apply Subgroup.card_eq_one.mp
        obtain ⟨n, hn⟩ := hP.exists_card_eq
        cases n with
        | zero => simpa using hn
        | succ n => exact (hd ((hn ▸ dvd_pow_self p (Nat.succ_ne_zero n)).trans
            (card_dvd_of_le hPF))).elim
      let : IsCyclic P := hbot ▸ inferInstanceAs (IsCyclic (⊥ : Subgroup L))
      exact isCyclic_of_injective (C.subtype.subgroupMap (S : Subgroup C))
        (fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : P => (z : L)) h)))⟩
  infer_instance

end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open ChapterA.Section03
open Theory.GroupTheory.LocalSolvableCoreNormalizer

private theorem exists_marked_involution
    {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (F : Subgroup X) [F.Normal]
    (ho : Nat.Coprime 2 (Nat.card F))
    (e : (X ⧸ F) ≃* SL(2,ZMod p)) (hp : 3 < p)
    (S : Sylow 2 ((center (X ⧸ F)).comap (QuotientGroup.mk' F))) :
    ∃ t : X, orderOf t = 2 ∧ t ∉ F ∧
      (S : Subgroup ((center (X ⧸ F)).comap (QuotientGroup.mk' F))).map
        ((center (X ⧸ F)).comap (QuotientGroup.mk' F)).subtype = zpowers t := by
  let q := QuotientGroup.mk' F
  let Z := center (X ⧸ F)
  let R := Z.comap q
  let Q := (S : Subgroup R).map R.subtype
  have hZ : Nat.card Z = 2 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact (GorensteinWalter.sl2ProjectiveProjection_ker (ZMod p)) ▸
      GorensteinWalter.sl2ProjectiveProjection_ker_card (ZMod p)
        (by simpa using (Fact.out : p.Prime).odd_of_ne_two (by omega))
  let r : R →* Z := q.subgroupComap Z
  have hr : Function.Surjective r := q.subgroupComap_surjective_of_surjective _
    (QuotientGroup.mk'_surjective F)
  have hStop : (S.mapSurjective hr : Subgroup Z) = ⊤ := by
    apply top_unique
    exact ((IsPGroup.of_card (p := 2) (n := 1) (by simpa using hZ)).to_subgroup ⊤).le_sylow_of_normal _
  have hmap : Q.map q = Z := by
    have hh := congrArg (Subgroup.map Z.subtype) hStop
    change ((S : Subgroup R).map r).map Z.subtype = (⊤ : Subgroup Z).map Z.subtype at hh
    rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact (map_map _ _ _).trans hh
  have hi := injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using ho) Q (S.isPGroup'.map R.subtype)
  let a : Q ≃* Q.map q := MulEquiv.ofBijective (q.subgroupMap Q)
    ⟨fun _ _ h => hi (congrArg Subtype.val h), q.subgroupMap_surjective Q⟩
  have hc : Nat.card Q = 2 := (Nat.card_congr a.toEquiv).trans (hmap ▸ hZ)
  let : IsCyclic Q := isCyclic_of_prime_card (p := 2) hc
  obtain ⟨t, ht⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp (inferInstance : IsCyclic Q)
  have ht2 : orderOf (t : X) = 2 := (Subgroup.orderOf_coe t).trans (ht.trans hc)
  have hgen : Q = zpowers (t : X) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr t.property) ?_).symm
    rw [Nat.card_zpowers, ht2, hc]
  refine ⟨t, ht2, ?_, hgen⟩
  intro hF
  have hq : q t = q 1 := by
    rw [map_one]
    exact (QuotientGroup.eq_one_iff (N := F) (t : X)).mpr hF
  have he : t = 1 := hi hq
  have hh := congrArg orderOf he
  rw [ht, hc, orderOf_one] at hh
  omega

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open ChapterA.Section03
open Theory.GroupTheory.LocalSolvableCoreNormalizer

private theorem radical_eq_center_preimage
    {X : Type*} [Group X] [Finite X] (F : Subgroup X) [F.Normal]
    [Group.IsSolvable F] [IsQuasisimple (X ⧸ F)] :
    solvableRadical X = (center (X ⧸ F)).comap (QuotientGroup.mk' F) := by
  let : Group.IsSolvable (center (X ⧸ F)) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  have hc : solvableRadical (X ⧸ F) = center (X ⧸ F) := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical _ inferInstance inferInstance)
  have hk : Group.IsSolvable (QuotientGroup.mk' F).ker := by
    rw [QuotientGroup.ker_mk']; infer_instance
  let := hk
  rw [← comap_solvableRadical_eq_of_solvable_ker (QuotientGroup.mk' F)
    (QuotientGroup.mk'_surjective _), hc]

/-- Recognize the residual for the specified Sylow intersection in the
noncentral Fitting quotient branch. -/
theorem radical_sylow_normalizer_residual_model
    {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    {𝒦 : CFSG.Quasithin.GroupClass} (hG : IsSQTK 𝒦 G) (hO : pCore 2 G = ⊥)
    (hL : L.IsCComponent) (hquot : NoncentralFitting.PrimeSL2FittingQuotient L)
    (P : Sylow 2 L) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ Nonempty
      (((solvableResidual (normalizer (((P : Subgroup L) ⊓ solvableRadical L : Subgroup L) : Set L))).map
        (normalizer (((P : Subgroup L) ⊓ solvableRadical L : Subgroup L) : Set L)).subtype) ≃*
          SL(2,ZMod p)) := by
  have hquot0 := hquot
  obtain ⟨p,hp,hp3,⟨e⟩⟩ := hquot
  let : Fact p.Prime := ⟨hp⟩
  let F := fittingSubgroup L
  let : IsQuasisimple (L ⧸ F) := NoncentralFitting.fitting_quotient_quasisimple hquot0
  have hrad : solvableRadical L =
      (center (L ⧸ F)).comap (QuotientGroup.mk' F) := radical_eq_center_preimage F
  have hFodd : Nat.Coprime 2 (Nat.card F) :=
    Nat.coprime_two_left.mpr (NoncentralFitting.fitting_odd_card hL hO)
  obtain ⟨S,hS⟩ := P.exists_subgroupOf_eq_of_normal
    ((center (L ⧸ F)).comap (QuotientGroup.mk' F))
  obtain ⟨t,ht2,htF,hSt⟩ := exists_marked_involution F hFodd e hp3 S
  have hPt : (P : Subgroup L) ⊓ solvableRadical L = zpowers t := by
    rw [hS,subgroupOf_map_subtype,← hrad] at hSt
    exact hSt
  have hcyc := NoncentralFitting.fixed_centralizer_isCyclic hG hO hL hquot0 t
    (ht2 ▸ pow_orderOf_eq_one t) htF
  obtain ⟨a,_⟩ :=
    CFSG.Quasithin.Chapter10.SourceOldResidualOddCoreNormalizerCover.exists_normalizer_residual_equiv_of_center_preimage_sylow
      hp3 F e t ht2 hcyc S hSt
  refine ⟨p,hp,hp3,?_⟩
  rw [hPt]
  exact ⟨a⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE ChapterA.Section03
open Theory.GroupTheory.LocalSolvableCoreNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original normalizer residual, mapped through the actual ambient
2-core quotient, is SL₂ over a prime field. -/
theorem cartan_normalizer_residual_prime_model
    {J : Subgroup G} (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hn : let N := normalizer (m.tensorLine : Set G)
      let I := (J.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
      ¬ fittingSubgroup I ≤ center I) :
    m.CartanNormalizerResidualPrimeModel J := by
  let N := normalizer (m.tensorLine : Set G)
  let JN := J.subgroupOf N
  let qN := QuotientGroup.mk' (pCore 2 N)
  let I := JN.map qN
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from
    ⟨m.tensorLine,m.tensorLine_ne_bot,IsPGroup.of_card (n := 2) m.card_tensorLine,rfl⟩)
  have hq : IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N) := by
    refine ⟨?_,hN.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hN.stronglyQuasithin p hp ho)
  let := (pCore_isPGroup (p := 2) (G := N)).isNilpotent
  have hFO := NoncentralFitting.noncentral_fitting_quotient_consequences
    ChapterA.RankActions.primeSL2CoverRigidity hq (pCore_quotient_pCore_eq_bot 2)
    (hJ.map_quotient (pCore 2 N)) hn
  have hquot : NoncentralFitting.PrimeSL2FittingQuotient I :=
    NoncentralFitting.primeSL2FittingQuotient_of_noncentral
      ChapterA.RankActions.primeSL2CoverRigidity hq (pCore_quotient_pCore_eq_bot 2)
      (hJ.map_quotient (pCore 2 N)) hn
  let j : JN ≃* J := subgroupOfEquivOfLe hJU
  have hR : twoOddTwoCore J = solvableRadical J := by
    let : Group.IsSolvable (pPrimeCore 2 I) :=
      hFO.1 ▸ inferInstanceAs (Group.IsSolvable (fittingSubgroup I))
    let ej : (J ⧸ pCore 2 J) ≃* I :=
      (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).symm.trans
        (cComponentTwoCoreQuotientEquiv hJ)
    let o : pPrimeCore 2 (J ⧸ pCore 2 J) ≃* pPrimeCore 2 I :=
      ((pPrimeCore 2 (J ⧸ pCore 2 J)).equivMapOfInjective ej.toMonoidHom ej.injective).trans
        (MulEquiv.subgroupCongr (pPrimeCore_map_iso 2 ej))
    let : Group.IsSolvable (pPrimeCore 2 (J ⧸ pCore 2 J)) :=
      Group.isSolvable_of_isSolvable_injective (f := o.toMonoidHom) o.injective
    let : IsQuasisimple (I ⧸ fittingSubgroup I) := hFO.2
    let : IsQuasisimple (I ⧸ pPrimeCore 2 I) :=
      IsQuasisimple.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hFO.1)
    let eq : ((J ⧸ pCore 2 J) ⧸ pPrimeCore 2 (J ⧸ pCore 2 J)) ≃* (I ⧸ pPrimeCore 2 I) :=
      QuotientGroup.congr _ _ ej (pPrimeCore_map_iso 2 ej)
    let : IsQuasisimple ((J ⧸ pCore 2 J) ⧸ pPrimeCore 2 (J ⧸ pCore 2 J)) :=
      IsQuasisimple.of_mulEquiv eq.symm
    exact twoOddTwoCore_eq_solvableRadical
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    m.tensorLine_normalized.trans ((normal_subgroupOf_iff_le_normalizer hJU).mp hnJ)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T J hTJ
  let f : J →* I := (qN.subgroupMap JN).comp j.symm.toMonoidHom
  have hf : Function.Surjective f := (qN.subgroupMap_surjective JN).comp j.symm.surjective
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((qN.subgroupMap JN).ker.comap j.symm.toMonoidHom)
    apply IsPGroup.comap_of_injective _ _ j.symm.injective
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let := hk.isNilpotent
  let U : Subgroup J :=
    (solvableResidual (normalizer (((P : Subgroup J) ⊓ solvableRadical J : Subgroup J) : Set J))).map
      (normalizer (((P : Subgroup J) ⊓ solvableRadical J : Subgroup J) : Set J)).subtype
  have hU : U.map J.subtype = localNormalizerResidual J
      ((T : Subgroup G) ⊓ (twoOddTwoCore J).map J.subtype) := by
    rw [hR]
    dsimp only [U]
    rw [hP]
    exact intrinsic_localNormalizerResidual J (T : Subgroup G) (solvableRadical J)
  have hmap := radical_normalizer_residual_map P f hf
  obtain ⟨p,hp,hp3,⟨a⟩⟩ := radical_sylow_normalizer_residual_model hq
    (pCore_quotient_pCore_eq_bot 2) (hJ.map_quotient (pCore 2 N)) hquot (P.mapSurjective hf)
  have htarget : m.cartanNormalizerResidualImage J = (U.map f).map I.subtype := by
    rw [cartanNormalizerResidualImage,← hU]
    exact subgroup_image_ambient_quotient N J hJU qN U
  exact ⟨p,hp,hp3,⟨(MulEquiv.subgroupCongr htarget).trans
    (((U.map f).equivMapOfInjective I.subtype I.subtype_injective).symm.trans
      ((MulEquiv.subgroupCongr hmap).trans a))⟩⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
