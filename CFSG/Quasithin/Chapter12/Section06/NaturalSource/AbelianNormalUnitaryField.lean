module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalUnitaryBorel
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.UnitaryBorelField
public import Theory.GroupTheory.Commutator.SplitPair
/-!
# Excluding the original even-degree unitary component

Cubic Borel displacement by the actual T intersect L becomes trivial on
its odd quotient by semilinear field rigidity. The original full commutator
identity and the checked direct-product splitting then put L₁-star inside
a two-group times its centralizing cubic. Its surviving Sylow E₉ contradicts
that order bound. All original quotient kernels and earlier geometry remain.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837, refs/quasithin.pdf.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
  {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hKH : K ≤ H)

include hz hTV hTz hbound hTI hns hH hKH in
/-- In even unitary degree the original Borel displacement lies in T intersect K. -/
theorem SourceHypothesis.original_abelian_normal_unitaryEven_borel_displacement
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n) (heven : Even n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) :
    ⁅(T : Subgroup G) ⊓ L,K ⊓ M L⁆ ≤ (T : Subgroup G) ⊓ K := by
  obtain ⟨P,hP,hB,_,hnB,_⟩ := S.original_abelian_normal_unitaryThree_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2 hm
  let B := K ⊓ M L
  let N := normalizer (P : Set K)
  let e : N ≃* B := (N.equivMapOfInjective K.subtype K.subtype_injective).trans
    (MulEquiv.subgroupCongr hB)
  have hPK : (P : Subgroup K) = (T : Subgroup G).subgroupOf K := by
    apply Subgroup.map_injective K.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  obtain ⟨hnBT,hodd,hcube⟩ := S.original_abelian_normal_unitaryThree_borel_torus_action
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2 hm
  have hcore := S.original_abelian_normal_unitaryThree_borel_core
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2 hm
  obtain ⟨F,hF,hfin,J,hcardF,hconj,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let X := BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J
  let q : K →* X := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup K) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  apply commutator_le.mpr
  intro s hs b hb
  let α := K.normalizerMonoidHom ⟨s,hTK hs.1⟩
  let β := MulAut.congr eK (quotientAut (pCore 2 K) α)
  have heq (x : K) : q (α x) = β (q x) := by
    change eK (QuotientGroup.mk' _ (α x)) =
      eK (quotientAut (pCore 2 K) α (eK.symm (eK (QuotientGroup.mk' _ x))))
    rw [eK.symm_apply_apply,quotientAut_apply_mk]
  have hαP : (P : Subgroup K).map α.toMonoidHom = P := by
    rw [hPK]
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      change s * (x : G) * s⁻¹ ∈ (T : Subgroup G)
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem hs.1 hx)
        ((T : Subgroup G).inv_mem hs.1)
    · intro x hx
      refine ⟨α.symm x,?_,α.apply_symm_apply x⟩
      have hi : α.symm = K.normalizerMonoidHom ⟨s⁻¹,(normalizer (K : Set G)).inv_mem (hTK hs.1)⟩ := by
        exact (map_inv K.normalizerMonoidHom ⟨s,hTK hs.1⟩).symm
      rw [hi]
      change s⁻¹ * (x : G) * s⁻¹⁻¹ ∈ (T : Subgroup G)
      rw [inv_inv]
      exact (T : Subgroup G).mul_mem
        ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem hs.1) hx) hs.1
  have hc (x : K) (hx : x ∈ normalizer (P : Set K)) :
      (α x * x⁻¹)^3 ∈ (P : Subgroup K) := by
    let b' : B := e ⟨x,hx⟩
    let aB := B.normalizerMonoidHom ⟨s,hnBT hs.1⟩
    have hh := hcube ⟨s,hs⟩ b'
    have hzq : QuotientGroup.mk' (pCore 2 B) ((aB b' * b'⁻¹)^3) = 1 := by
      simpa only [map_pow,map_mul,map_inv] using hh
    have hmem := (QuotientGroup.eq_one_iff _).mp hzq
    have him := mem_map_of_mem B.subtype hmem
    change ((aB b' * b'⁻¹)^3 : B).val ∈ B.pCoreIn 2 at him
    rw [hcore] at him
    rw [hPK]
    exact him.1
  have hstep := UnitaryBorelField.normalizer_displacement_mem_of_cube J hn2 heven
    hcardF hconj q hq P hk α β heq hαP hc
  let b' : B := ⟨b,hb⟩
  let x : N := e.symm b'
  have hd : α (x : K) * (x : K)⁻¹ ∈ (P : Subgroup K) := hstep x x.property
  have him := mem_map_of_mem K.subtype hd
  rw [hP] at him
  have heval : ((x : K) : G) = b := congrArg Subtype.val (e.apply_symm_apply b')
  change s * ((x : K) : G) * s⁻¹ * (((x : K) : G))⁻¹ ∈ (T : Subgroup G) ⊓ K at him
  simpa only [heval,commutatorElement_def] using him

variable (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original normal PSU₃ component cannot have even field degree. -/
theorem SourceHypothesis.original_abelian_normal_unitaryEven_excluded
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n) (heven : Even n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) : False := by
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  let C := A ⊓ centralizer (B : Set (H ⧸ pCore 2 H))
  let U := actorImage H ((T : Subgroup G) ⊓ L)
  let X := actorImage H ((T : Subgroup G) ⊓ K)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  obtain ⟨hCn,_,hCc,hs,_⟩ := S.original_abelian_normal_unitaryEven_split
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 heven hm
  let : C.Normal := hCn
  have hAM : A ≤ actorImage H (M L) := map_mono (comap_mono
    ((map_subtype_le _).trans (inf_le_left.trans L.le_normalizer)))
  have hkM : (QuotientGroup.mk' (pCore 2 H)).ker ≤ (M L).subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    intro x hx
    exact S.chosen.sylow_normalizes_component
      ((S.original_point_core_eq D hZ z hz hTz).2.2
        (S.original_core_le_point_core D hZ z hH (mem_map_of_mem H.subtype hx)))
  have him : actorImage H (K ⊓ M L) = B ⊓ actorImage H (M L) := by
    change ((K ⊓ M L).comap H.subtype).map (QuotientGroup.mk' (pCore 2 H)) =
      (K.comap H.subtype).map (QuotientGroup.mk' (pCore 2 H)) ⊓
        ((M L).comap H.subtype).map (QuotientGroup.mk' (pCore 2 H))
    rw [comap_inf]
    exact map_inf_of_ker_le _ _ _ hkM
  have hAB : A ⊓ B ≤ actorImage H (K ⊓ M L) := by
    rw [him]
    exact le_inf inf_le_right (inf_le_left.trans hAM)
  have hmov : ⁅actorImage H (K ⊓ M L),U⁆ ≤ X := by
    have hh := S.original_abelian_normal_unitaryEven_borel_displacement
      D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2 heven hm
    rw [commutator_comm] at hh
    unfold U X actorImage
    rw [←map_commutator,
      ←SubgroupTransport.subgroupOf_commutator _ _ (inf_le_left.trans hKH) (inf_le_left.trans hTH)]
    exact map_mono (comap_mono hh)
  have hfull : ⁅A,U⁆ = A := by
    unfold A U actorImage
    rw [←map_commutator,
      ←SubgroupTransport.subgroupOf_commutator _ _ hLH (inf_le_left.trans hTH),
      S.original_point_residual_full_commutator D hZ z hz hTz]
  have hcomm : (A ⊓ B) ≤ centralizer (C : Set (H ⧸ pCore 2 H)) :=
    inf_le_right.trans (le_centralizer_iff.mp (show C ≤ centralizer (B : Set _) from inf_le_right))
  have hAC : A ≤ X ⊔ C := by
    change A = (A ⊓ B) ⊔ C at hs
    calc
      A = ⁅A,U⁆ := hfull.symm
      _ = ⁅(A ⊓ B) ⊔ C,U⁆ := congrArg (fun Y => ⁅Y,U⁆) hs
      _ = ⁅A ⊓ B,U⁆ ⊔ ⁅C,U⁆ :=
        commutator_sup_of_commuting_factors _ _ U hcomm le_normalizer_of_normal
      _ ≤ X ⊔ C := sup_le ((commutator_mono hAB le_rfl).trans hmov |>.trans le_sup_left)
        ((le_normalizer_iff_commutator_le_left.mp
          (le_normalizer_of_normal : U ≤ normalizer (C : Set _))).trans le_sup_right)
  have h9 : 9 ∣ Nat.card A := by
    let P : Sylow 3 E.L₁ := Classical.choice inferInstance
    let P₀ := (P : Subgroup E.L₁).map E.L₁.subtype
    have hPA : actorImage H P₀ ≤ A := map_mono (comap_mono (map_subtype_le _))
    have hh := card_dvd_of_le hPA
    have hp := (S.original_point_sylow_star D hZ z hz hTz hH P).2.1
    change Nat.card (actorImage H P₀) = 9 at hp
    rwa [hp] at hh
  have hX : IsPGroup 2 X :=
    ((T.isPGroup'.to_le (show (T : Subgroup G) ⊓ K ≤ T from inf_le_left)).comap_subtype).map _
  obtain ⟨r,hr⟩ := hX.exists_card_eq
  have hCX : C ≤ centralizer (X : Set (H ⧸ pCore 2 H)) :=
    (show C ≤ centralizer (B : Set _) from inf_le_right).trans
      (centralizer_le (map_mono (comap_mono inf_le_right)))
  have hcount := card_mul_eq_card_inf_mul_card_sup_of_normalizes X C
    (hCX.trans (Subgroup.centralizer_le_normalizer _))
  have hdiv : Nat.card (X ⊔ C : Subgroup (H ⧸ pCore 2 H)) ∣ Nat.card X * Nat.card C := by
    rw [hcount]
    exact dvd_mul_left _ _
  have hh := h9.trans ((card_dvd_of_le hAC).trans hdiv)
  rw [hr,hCc] at hh
  have hh3 : 3 ∣ 2^r := (mul_dvd_mul_iff_right (by decide : (3:ℕ) ≠ 0)).mp hh
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hh3)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- Any surviving original projective unitary-three parameter is odd. -/
theorem SourceHypothesis.original_abelian_normal_unitaryThree_odd
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 (2 ^ n)) : Odd n := by
  exact Nat.not_even_iff_odd.mp (fun he =>
    S.original_abelian_normal_unitaryEven_excluded D hZ z hz hTV hTz hbound hTI hns
      hH hKH hK hgen hn hout hn2 he hm)
end CFSG.Quasithin.Chapter12.Section06
