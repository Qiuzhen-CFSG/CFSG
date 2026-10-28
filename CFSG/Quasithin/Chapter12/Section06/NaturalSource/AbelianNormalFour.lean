module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianNormalSplit
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianExchangedTorus
public import Theory.SpecificGroups.SL2.SylowNormalizerCubicAction
public import Theory.GroupTheory.Commutator.SplitPair
/-!
# Field order four in the original normal PSL₂ branch

On the literal Borel K intersect M, every displacement by T intersect L
has cubic image under the Sylow-normalizer character. The character
intertwines this action with a field automorphism. Above field order
four, fixing all cubes forces that field automorphism to be trivial;
hence [T intersect L,K intersect M] lies in the original T intersect K.

Apply the direct-product splitting of L₁-star and the original identity
L₁=[L₁,T intersect L]. The preceding displacement containment puts all
of L₁-star in (T intersect K)-star times its centralizing cubic. This
product has three-part at most three, whereas the original Sylow E₉
survives O₂(H), a contradiction. Thus n=2. Both original component
quotients are consequently PSL₂(4), with the same marked Borel.

Source: Aschbacher--Smith 12.6.31, printed pp.836--837, refs/quasithin.pdf.
The relative normality, escaping component, actual reduced actor and
earlier geometric hypotheses are retained. The signed degree-three,
symplectic and G₂ rows, subsequent module exclusions and universal
NaturalReduction remain obligations of the source assembly.
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
/-- Above field order four the original Borel displacement lies in T intersect K. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_borel_displacement
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 < n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    ⁅(T : Subgroup G) ⊓ L,K ⊓ M L⁆ ≤ (T : Subgroup G) ⊓ K := by
  obtain ⟨P,hP,hB,_,hnB,_⟩ := S.original_abelian_normal_linearTwo_borel
    D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hn2.le hm
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
  obtain ⟨F,hF,hfin,hcardF,⟨eK⟩⟩ := hm
  let := hF
  let := hfin
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  let eQ := eK.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  let q : K →* SL(2,F) := eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eQ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker ≤ (P : Subgroup K) := by
    rw [MonoidHom.ker_comp_of_injective _ _ eQ.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have ho : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units,hcardF]
    have hpow : Even (2^n) := even_two.pow_of_ne_zero (by omega)
    exact Nat.Even.sub_odd (Nat.one_le_pow n 2 (by decide)) hpow odd_one
  apply commutator_le.mpr
  intro s hs b hb
  let α := K.normalizerMonoidHom ⟨s,hTK hs.1⟩
  let β := MulAut.congr eQ (quotientAut (pCore 2 K) α)
  have heq (x : K) : q (α x) = β (q x) := by
    change eQ (QuotientGroup.mk' _ (α x)) =
      eQ (quotientAut (pCore 2 K) α (eQ.symm (eQ (QuotientGroup.mk' _ x))))
    rw [eQ.symm_apply_apply,quotientAut_apply_mk]
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
  obtain ⟨f,σ,hf,hfk,hact⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_torus_action
    q hq P hk α β heq hαP
  have hnN : N.map α.toMonoidHom = N := by
    change (normalizer (P : Set K)).map α.toMonoidHom = normalizer (P : Set K)
    have hh := map_normalizer_eq_of_bijective (P : Subgroup K) (f := α.toMonoidHom) α.bijective
    rw [hαP] at hh
    simpa only [Sylow.coe_coe] using hh
  let a : MulAut N := (α.subgroupMap N).trans (MulEquiv.subgroupCongr hnN)
  have hc (x : N) : (f (a x) * (f x)⁻¹)^3 = 1 := by
    let fB : B →* Fˣ := f.comp e.symm.toMonoidHom
    have h := S.original_point_normalizer_odd_displacement_cube D hZ z hz hTz B inf_le_right
      (inf_le_left.trans (hKH.trans hH.2.1)) (le_sup_right.trans hnB) fB ho ⟨s,hs⟩ (e x)
    have hconj : B.normalizerMonoidHom ⟨s,(le_sup_right.trans hnB) hs.1⟩ (e x) = e (a x) := by
      apply Subtype.ext
      rfl
    rw [hconj] at h
    simpa only [fB,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.symm_apply_apply] using h
  have hσ : σ = 1 := by
    apply (FiniteField.eq_one_or_card_le_four_of_unit_displacement_cube σ ?_).resolve_right
    · intro hsmall
      have hlt : 2^2 < 2^n := Nat.pow_lt_pow_right (by decide) hn2
      rw [←hcardF] at hlt
      omega
    · intro u
      obtain ⟨x,rfl⟩ := hf u
      rw [←hact x (a x) rfl]
      exact hc x
  let b' : B := ⟨b,hb⟩
  let x : N := e.symm b'
  have hfix : f (a x) = f x := by
    rw [hact x (a x) rfl,hσ]
    rfl
  have hd : (a x : K) * (x : K)⁻¹ ∈ (P : Subgroup K) :=
    (hfk (a x * x⁻¹)).mp (by rw [map_mul,map_inv,hfix,mul_inv_cancel])
  have him := mem_map_of_mem K.subtype hd
  rw [hP] at him
  have heval : ((x : K) : G) = b := congrArg Subtype.val (e.apply_symm_apply b')
  change s * ((x : K) : G) * s⁻¹ * (((x : K) : G))⁻¹ ∈ (T : Subgroup G) ⊓ K at him
  simpa only [heval,commutatorElement_def] using him

variable (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔
    (T : Subgroup G) = H)

include hz hTV hTz hbound hTI hns hH hKH hK hgen in
/-- The original normal PSL₂ component has field order four. The original
full T intersection L commutator rules out a larger even field. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_field_eq_two
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) : n = 2 := by
  by_contra hne
  have hgt : 2 < n := by omega
  let E := D.fullSetup hZ T z
  let A := actorImage H E.L₁
  let B := actorImage H K
  let C := A ⊓ centralizer (B : Set (H ⧸ pCore 2 H))
  let U := actorImage H ((T : Subgroup G) ⊓ L)
  let X := actorImage H ((T : Subgroup G) ⊓ K)
  have hLH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hTH : (T : Subgroup G) ≤ H := fun x hx => hH.1.2 (Or.inr hx)
  obtain ⟨hs,_,_⟩ := S.original_abelian_normal_linearTwo_split
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
  obtain ⟨hCn,_,hCc⟩ := S.original_abelian_normal_linearTwo_centralizer_card
    D hZ z hz hTV hTz hH hKH hK hgen hn hn2 hm
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
    have hh := S.original_abelian_normal_linearTwo_borel_displacement
      D hZ z hz hTV hTz hbound hTI hns hH hKH hn hout hgt hm
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
/-- Both original quotient carriers are PSL₂(4); their actual Borel image has order twelve. -/
theorem SourceHypothesis.original_abelian_normal_linearTwo_four
    (hn : (K.subgroupOf H).Normal) (hout : ¬ K ≤ M L)
    {n : ℕ} (hn2 : 2 ≤ n)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ n)) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
      ClassicalGroup.IsPSL (actorImage H K) 2 4 ∧
      Nat.card (actorImage H (K ⊓ M L)) = 12 := by
  have hn4 := S.original_abelian_normal_linearTwo_field_eq_two
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hgen hn hout hn2 hm
  subst n
  refine ⟨hm,hm.of_mulEquiv (componentStarEquiv H K hKH hK).symm,?_⟩
  simpa using S.original_abelian_normal_linearTwo_borel_star_card
    D hZ z hz hTV hTz hbound hTI hns hH hKH hK hn hout hn2 hm

end CFSG.Quasithin.Chapter12.Section06
