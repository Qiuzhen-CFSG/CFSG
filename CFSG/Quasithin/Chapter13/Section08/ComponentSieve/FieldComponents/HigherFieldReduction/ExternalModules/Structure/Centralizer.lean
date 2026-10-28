module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.Quotient
public import Theory.GroupTheory.InvertedCubicTwoExtension
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.SmallFittingResidual

/-!
# The actual centralizer and its inverted cubic subgroup

Relative normality in H makes C = C_{H*}(K*) normal, so its two-core
vanishes. If K* is centerless and K*X* has a two-group supplement, then
C/X* embeds in H*/K*X*: an element of C ∩ K*X* has trivial K* coordinate.
Alternatively, a solvable supplement and the earlier bound F(H*) ≤ X*
make C solvable with F(C) ≤ X*. Its two-residual centralizes the cubic
X*, so solvable Fitting self-centralization puts that residual in X*.
This proves directly that C/X* is a two-group.

Recognition of the inverted cubic extension constructs an injective S₃
homomorphism into H*, mapping its actual alternating subgroup onto X*.

Source: Aschbacher–Smith, proof of 13.8.20(a), combined manuscript of
1 March 2004, printed p.954 (PDF p.971). Centerlessness and the earlier Fitting data remain explicit in these
conditional deductions; the source adapter supplies the latter using
13.8.14 and H = KL₁T. No isomorphism
C ≃ S₃, nor the vanishing of O₂(C), is assumed.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure
variable {G : Type*} [Group G] [Finite G]

/-- Relative component normality makes its actual centralizer two-reduced. -/
theorem centralizer_twoCore (H K : Subgroup G) [(K.subgroupOf H).Normal] :
    pCore 2 (centralizer (Source.starImage H K : Set (Source.Hstar H))) = ⊥ := by
  let : (Source.starImage H K).Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  let C := centralizer (Source.starImage H K : Set (Source.Hstar H))
  have hQ : pCore 2 (Source.Hstar H) = ⊥ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    have he := congrArg (map q)
      (q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk)
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at he
    exact he.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  have hle : (pCore 2 C).map C.subtype ≤ pCore 2 (Source.Hstar H) :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map C.subtype⟩
  apply bot_unique
  intro c hc
  apply Subtype.ext
  exact mem_bot.mp (hQ ▸ hle (mem_map.mpr ⟨c,hc,rfl⟩))

private theorem centralizer_quotient_twoGroup {D : Type*} [Group D]
    (K X : Subgroup D) [K.Normal] [X.Normal]
    (hcent : X ≤ centralizer (K : Set D)) (hz : center K = ⊥)
    (hq : IsPGroup 2 (D ⧸ (K ⊔ X))) :
    IsPGroup 2 (centralizer (K : Set D) ⧸ X.subgroupOf (centralizer (K : Set D))) := by
  let C := centralizer (K : Set D)
  let f : C →* D ⧸ (K ⊔ X) := (QuotientGroup.mk' (K ⊔ X)).comp C.subtype
  have hker : f.ker = X.subgroupOf C := by
    ext c
    change QuotientGroup.mk' (K ⊔ X) c.val = 1 ↔ c.val ∈ X
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hc
      obtain ⟨k,hk,x,hx,he⟩ := mem_sup_of_normal_left.mp hc
      have hkC : k ∈ C := by
        have hk' : k = c.val * x⁻¹ := by rw [← he]; group
        rw [hk']
        exact C.mul_mem c.property (C.inv_mem (hcent hx))
      have hkz : (⟨k,hk⟩ : K) ∈ center K := by
        rw [Subgroup.mem_center_iff]
        intro y
        apply Subtype.ext
        exact hkC y y.property
      have hk1 : k = 1 := congrArg (fun a : K => a.val) (mem_bot.mp (hz ▸ hkz))
      have heq : x = c.val := by simpa only [hk1, one_mul] using he
      exact heq ▸ hx
    · exact fun hx => (show X ≤ K ⊔ X from le_sup_right) hx
  let g := QuotientGroup.lift (X.subgroupOf C) f hker.ge
  exact hq.of_injective g ((QuotientGroup.injective_lift_iff _ _ _).mpr hker.symm)

private theorem centralizer_twoQuotient_of_small_fitting {D : Type*} [Group D] [Finite D]
    (K X P : Subgroup D) [K.Normal] [X.Normal] [Group.IsSolvable P]
    (hcent : X ≤ centralizer (K : Set D)) (hz : center K = ⊥)
    (hcard : Nat.card X = 3) (hgen : K ⊔ P = ⊤)
    (hfit : fittingSubgroup D ≤ X) :
    IsPGroup 2 (centralizer (K : Set D) ⧸ X.subgroupOf (centralizer (K : Set D))) := by
  let C := centralizer (K : Set D)
  let Y := X.subgroupOf C
  let q := QuotientGroup.mk' K
  have hmap : P.map q = ⊤ := by
    have he := congrArg (map q) hgen
    simpa only [q, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using he
  have hf : Function.Surjective (q.comp P.subtype) := by
    intro y
    have hy : y ∈ P.map q := by rw [hmap]; trivial
    obtain ⟨p,hp,he⟩ := hy
    exact ⟨⟨p,hp⟩,he⟩
  let : Group.IsSolvable (D ⧸ K) := Group.isSolvable_of_surjective hf
  have hC : Group.IsSolvable C := centralizer_solvable_of_centerless_quotient K hz
  have hCY : fittingSubgroup C ≤ Y := by
    have hFC : fittingSubgroupOf C ≤ fittingSubgroup D :=
      le_sSup ⟨fittingSubgroupOf_normal C inferInstance, fittingSubgroupOf_isNilpotent C⟩
    intro c hc
    exact hfit (hFC ⟨c,hc,rfl⟩)
  have hycard : Nat.card Y = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hcent).toEquiv).trans hcard
  have hRY : pResidual 2 C ≤ Y := by
    have hc := twoPerfect_centralizes_small_normal
      (pResidual 2 C) Y
      (isPPerfect_pResidual 2) (Or.inr hycard)
    intro c hcR
    apply hCY
    apply centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hC
    intro b hb
    exact hc hcR b (hCY hb)
  intro y
  obtain ⟨c,rfl⟩ := QuotientGroup.mk'_surjective Y y
  obtain ⟨n,hn⟩ := isPGroup_quotient_pResidual (G := C) 2
    (QuotientGroup.mk' (pResidual 2 C) c)
  refine ⟨n, ?_⟩
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  apply hRY
  apply (QuotientGroup.eq_one_iff _).mp
  change QuotientGroup.mk' (pResidual 2 C) (c ^ 2 ^ n) = 1
  simpa only [map_pow] using hn

/-- A centerless component and a two-group outer supplement suffice; no
recognition of the centralizer is assumed. -/
theorem symmetric_embedding (H K X : Subgroup G)
    [(K.subgroupOf H).Normal] [(X.subgroupOf H).Normal]
    (hcent : Source.starImage H X ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hz : center (Source.starImage H K) = ⊥)
    (hcard : Nat.card (Source.starImage H X) = 3)
    (T : Subgroup (Source.Hstar H)) (hT : IsPGroup 2 T)
    (hgen : (Source.starImage H K ⊔ Source.starImage H X) ⊔ T = ⊤)
    (hinv : ∃ c ∈ centralizer (Source.starImage H K : Set (Source.Hstar H)),
      ∀ x ∈ Source.starImage H X, c * x * c⁻¹ = x⁻¹) :
    ∃ s : Equiv.Perm (Fin 3) →* Source.Hstar H,
      Function.Injective s ∧
      s.range ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      (alternatingGroup (Fin 3)).map s = Source.starImage H X := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let C := centralizer (Ks : Set (Source.Hstar H))
  let Y := Xs.subgroupOf C
  let : Ks.Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  let : Xs.Normal := (inferInstance : (X.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  have hc : Nat.card Y = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hcent).toEquiv).trans hcard
  have hq : IsPGroup 2 (Source.Hstar H ⧸ (Ks ⊔ Xs)) :=
    quotient_isPGroup_of_sup_eq_top T (Ks ⊔ Xs) hT (by rwa [sup_comm])
  have hy : IsPGroup 2 (C ⧸ Y) := centralizer_quotient_twoGroup Ks Xs hcent hz hq
  obtain ⟨c,hcC,hci⟩ := hinv
  obtain ⟨e,he⟩ := InvertedCubicTwoExtension.exists_equiv_preserving_cubic Y hc hy
    (centralizer_twoCore H K) ⟨c,hcC⟩ (by
      intro x hx
      apply Subtype.ext
      exact hci x.val hx)
  let s := C.subtype.comp e.symm.toMonoidHom
  refine ⟨s, C.subtype_injective.comp e.symm.injective, ?_, ?_⟩
  · rintro _ ⟨g,rfl⟩
    exact (e.symm g).property
  · change (alternatingGroup (Fin 3)).map (C.subtype.comp e.symm.toMonoidHom) = Xs
    rw [← he, map_map]
    have hh : (C.subtype.comp e.symm.toMonoidHom).comp e.toMonoidHom = C.subtype := by ext; simp
    rw [hh]
    exact map_subgroupOf_eq_of_le hcent

/-- The earlier Fitting bound and a solvable supplement suffice to construct
the symmetric-three action; no two-group quotient of the centralizer is assumed. -/
theorem symmetric_embedding_of_small_fitting (H K X : Subgroup G)
    [(K.subgroupOf H).Normal] [(X.subgroupOf H).Normal]
    (hcent : Source.starImage H X ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hz : center (Source.starImage H K) = ⊥)
    (hcard : Nat.card (Source.starImage H X) = 3)
    (P : Subgroup (Source.Hstar H)) [Group.IsSolvable P]
    (hgen : Source.starImage H K ⊔ P = ⊤)
    (hfit : fittingSubgroup (Source.Hstar H) ≤ Source.starImage H X)
    (hinv : ∃ c ∈ centralizer (Source.starImage H K : Set (Source.Hstar H)),
      ∀ x ∈ Source.starImage H X, c * x * c⁻¹ = x⁻¹) :
    ∃ s : Equiv.Perm (Fin 3) →* Source.Hstar H,
      Function.Injective s ∧
      s.range ≤ centralizer (Source.starImage H K : Set (Source.Hstar H)) ∧
      (alternatingGroup (Fin 3)).map s = Source.starImage H X := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let C := centralizer (Ks : Set (Source.Hstar H))
  let Y := Xs.subgroupOf C
  let : Ks.Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  let : Xs.Normal := (inferInstance : (X.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  have hc : Nat.card Y = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hcent).toEquiv).trans hcard
  have hy : IsPGroup 2 (C ⧸ Y) :=
    centralizer_twoQuotient_of_small_fitting Ks Xs P hcent hz hcard hgen hfit
  obtain ⟨c,hcC,hci⟩ := hinv
  obtain ⟨e,he⟩ := InvertedCubicTwoExtension.exists_equiv_preserving_cubic Y hc hy
    (centralizer_twoCore H K) ⟨c,hcC⟩ (by
      intro x hx
      apply Subtype.ext
      exact hci x.val hx)
  let s := C.subtype.comp e.symm.toMonoidHom
  refine ⟨s, C.subtype_injective.comp e.symm.injective, ?_, ?_⟩
  · rintro _ ⟨g,rfl⟩
    exact (e.symm g).property
  · change (alternatingGroup (Fin 3)).map (C.subtype.comp e.symm.toMonoidHom) = Xs
    rw [← he, map_map]
    have hh : (C.subtype.comp e.symm.toMonoidHom).comp e.toMonoidHom = C.subtype := by ext; simp
    rw [hh]
    exact map_subgroupOf_eq_of_le hcent

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure

end
