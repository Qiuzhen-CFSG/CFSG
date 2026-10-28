module

public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import Theory.Representation.BinaryOffender.FixedQuotientEquality
public import Theory.Representation.SL2NaturalOffenders.PairPointwiseFixer
/-!
# Thompson and Baumann images on two natural factors

A moving maximum elementary subgroup can activate only one natural factor.
Its image nevertheless splits into full defining Sylows on its active factors.
A literal factor-exchanging element of the original Sylow subgroup activates
the other factor in the Thompson image. Thus that image is the Sylow
intersection with the normal product layer.

Every maximum elementary image has sharp fixed codimension. Intersecting
their fixed spaces gives the full inverse image of the quotient fixed space
for the Thompson subgroup, without requiring an individual maximum image
to equal the full product. The original pointwise centralizer argument and
the paired scalar-normalizer calculation then identify the Baumann image.

The actual centralizer kernel, original module and best-offender layer are
retained. The field with two elements is included.
Source: Aschbacher–Smith B.2.20, B.6.10 and E.2.3(2), pp.82,117,216–217.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => Matrix.SpecialLinearGroup (Fin 2) F
local notation "V" => Fin 2 → F

omit [Algebra (ZMod 2) F] in
private theorem pair_sylow (R : Sylow 2 (D × D)) :
    ∃ P Q : Sylow 2 D, (R : Subgroup (D × D)) = (P : Subgroup D).prod Q := by
  let P := R.mapSurjective (f := MonoidHom.fst D D) (fun g => ⟨(g,1),rfl⟩)
  let Q := R.mapSurjective (f := MonoidHom.snd D D) (fun g => ⟨(1,g),rfl⟩)
  have hp : IsPGroup 2 (P × Q) := by
    obtain ⟨m,hm⟩ := P.isPGroup'.exists_card_eq
    obtain ⟨n,hn⟩ := Q.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (n := m+n) (by rw [Nat.card_prod,hm,hn,pow_add])
  refine ⟨P,Q,(R.is_maximal' (hp.of_equiv ((P : Subgroup D).prodEquiv (Q : Subgroup D)).symm) ?_).symm⟩
  intro x hx
  exact ⟨mem_map_of_mem (MonoidHom.fst D D) hx,mem_map_of_mem (MonoidHom.snd D D) hx⟩

omit [Algebra (ZMod 2) F] in
private theorem pair_sylow_inf (L : Subgroup H) [L.Normal] (e : L ≃* D × D)
    (T : Sylow 2 H) : ∃ P Q : Sylow 2 D,
      (T : Subgroup H) ⊓ L = ((P : Subgroup D).prod Q).map (L.subtype.comp e.symm.toMonoidHom) := by
  obtain ⟨R,hR⟩ := T.exists_sylow_map_eq_inf_of_normal L
  obtain ⟨P,Q,hPQ⟩ := pair_sylow (R.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hPQ' : (R : Subgroup L).map e.toMonoidHom = (P : Subgroup D).prod Q := hPQ
  refine ⟨P,Q,?_⟩
  rw [←hR,←hPQ',Subgroup.map_map]
  congr 1
  ext x
  simp

/-- The actual Thompson image stays in the genuine best-offender layer. -/
theorem thompson_image_le_offender_layer
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G)) (hUT : U ≤ T)
    (L : Subgroup H)
    (hY : offenderSubgroup (NormalElementaryQuotient.representation U q hq hker) ≤ L) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ L := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro B hB
  apply map_le_iff_le_comap.mp
  by_cases hb : B.map q = ⊥
  · exact hb ▸ bot_le
  · exact (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      U q hq hker (T : Subgroup G) B hUT hB hb).le_offenderSubgroup _ |>.trans hY


theorem pair_offender_contains_axis
    (P Q : Sylow 2 D) (B : Subgroup (D × D))
    (hB : IsOffender (SL2NaturalOffenders.naturalPair (F := F)) B)
    (hle : B ≤ (P : Subgroup D).prod Q) :
    (P : Subgroup D).prod ⊥ ≤ B ∨ (⊥ : Subgroup D).prod Q ≤ B := by
  obtain ⟨R,S,hs,hR,hS⟩ := SL2NaturalOffenders.naturalPair_offender hB
  have h₁ : B.map (MonoidHom.fst D D) ≤ P := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hle hx).1
  have h₂ : B.map (MonoidHom.snd D D) ≤ Q := by
    rintro _ ⟨x,hx,rfl⟩
    exact (hle hx).2
  rcases hR with hR | hR
  · rcases hS with hS | hS
    · have hb : B = ⊥ := by rw [hs,hR,hS]; ext x; simp [Prod.ext_iff]
      exact (hB.1.1 hb).elim
    · have he : (S : Subgroup D) = Q := (S.is_maximal' Q.isPGroup' (hS ▸ h₂)).symm
      right
      rw [hs,hS,he]
      exact Subgroup.prod_mono bot_le le_rfl
  · have he : (R : Subgroup D) = P := (R.is_maximal' P.isPGroup' (hR ▸ h₁)).symm
    left
    rw [hs,hR,he]
    exact Subgroup.prod_mono le_rfl bot_le

omit [Finite H] in
/-- Sharpness for every moving maximum elementary subgroup gives a fixed lift
for their generated Thompson subgroup; their individual images may differ. -/
theorem thompson_fixedSpace_of_sharp_maxima
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (ρ : Representation (ZMod 2) H (V × V))
    (f : Additive U →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (f v))
    (hsharp : ∀ B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), B.map q ≠ ⊥ →
      fixedCodim (NormalElementaryQuotient.representation U q hq hker) (B.map q) =
        fixedCodim ρ (B.map q)) :
    fixedSpace (NormalElementaryQuotient.representation U q hq hker)
      ((elementaryAbelianMaxJ (T : Subgroup G)).map q) =
    (fixedSpace ρ ((elementaryAbelianMaxJ (T : Subgroup G)).map q)).comap f := by
  let α := NormalElementaryQuotient.representation U q hq hker
  apply le_antisymm
  · intro u hu g
    change ρ (g : H) (f u) = f u
    rw [←he]
    exact congrArg f (hu g)
  · intro u hu
    let C : Subgroup G := centralizer ({(u.toMul : G)} : Set G)
    have hJC : elementaryAbelianMaxJ (T : Subgroup G) ≤ C := by
      apply sSup_le
      intro B hB
      have hfix : u ∈ fixedSpace α (B.map q) := by
        by_cases hb : B.map q = ⊥
        · rw [hb,fixedSpace_bot]; trivial
        · rw [fixedSpace_eq_comap_of_fixedCodim_eq α ρ f hf he _ (hsharp B hB hb)]
          intro g
          exact hu ⟨g,map_mono (le_sSup hB) g.property⟩
      have hc := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker B u).mp hfix
      intro b hb
      change b ∈ centralizer ({(u.toMul : G)} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact hc b hb
    apply (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker _ u).mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hJC hx)


omit [Algebra (ZMod 2) F] [Finite G] [Finite H] [Finite F] in
private theorem pair_activation
    (η : D × D →* H) (hη : Function.Injective η)
    (P Q : Subgroup D) (J : Subgroup H) (τ : H ≃* H)
    (hJ : J.map τ.toMonoidHom = J)
    (hS : ((P.prod Q).map η).map τ.toMonoidHom = (P.prod Q).map η)
    (hK₁ : (((⊤ : Subgroup D).prod ⊥).map η).map τ.toMonoidHom =
      ((⊥ : Subgroup D).prod ⊤).map η)
    (hK₂ : (((⊥ : Subgroup D).prod ⊤).map η).map τ.toMonoidHom =
      ((⊤ : Subgroup D).prod ⊥).map η)
    (haxis : (P.prod ⊥).map η ≤ J ∨ ((⊥ : Subgroup D).prod Q).map η ≤ J) :
    (P.prod Q).map η ≤ J := by
  have h₁ : (P.prod Q).map η ⊓ (((⊤ : Subgroup D).prod ⊥).map η) =
      (P.prod ⊥).map η := by
    rw [←Subgroup.map_inf _ _ η hη]
    congr 1
    ext x
    simp only [mem_inf,mem_prod,mem_top,mem_bot]
    constructor
    · tauto
    · rintro ⟨h,hx⟩
      exact ⟨⟨h,hx ▸ Q.one_mem⟩,trivial,hx⟩
  have h₂ : (P.prod Q).map η ⊓ (((⊥ : Subgroup D).prod ⊤).map η) =
      ((⊥ : Subgroup D).prod Q).map η := by
    rw [←Subgroup.map_inf _ _ η hη]
    congr 1
    ext x
    simp only [mem_inf,mem_prod,mem_top,mem_bot]
    constructor
    · tauto
    · rintro ⟨hx,h⟩
      exact ⟨⟨hx ▸ P.one_mem,h⟩,hx,trivial⟩
  have hx : ((P.prod ⊥).map η).map τ.toMonoidHom = ((⊥ : Subgroup D).prod Q).map η := by
    rw [←h₁,Subgroup.map_inf _ _ _ τ.injective,hS,hK₁,h₂]
  have hy : (((⊥ : Subgroup D).prod Q).map η).map τ.toMonoidHom = (P.prod ⊥).map η := by
    rw [←h₂,Subgroup.map_inf _ _ _ τ.injective,hS,hK₂,h₁]
  have hboth : (P.prod ⊥).map η ≤ J ∧ ((⊥ : Subgroup D).prod Q).map η ≤ J := by
    rcases haxis with h | h
    · exact ⟨h, hx ▸ hJ ▸ Subgroup.map_mono h⟩
    · exact ⟨hy ▸ hJ ▸ Subgroup.map_mono h,h⟩
  rintro _ ⟨x,hx,rfl⟩
  have hh : x = (x.1,1) * (1,x.2) := by ext <;> simp
  rw [hh,map_mul]
  exact J.mul_mem (hboth.1 (mem_map.mpr ⟨(x.1,1),⟨hx.1,by simp⟩,rfl⟩))
    (hboth.2 (mem_map.mpr ⟨(1,x.2),⟨by simp,hx.2⟩,rfl⟩))


/-- Two natural factors with a literal exchanging element identify the original
Thompson and Baumann images. The genuine offender layer is retained. -/
theorem paired_images_and_fixedSpace
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (L : Subgroup H) [L.Normal] (e : L ≃* D × D)
    (ρ : Representation (ZMod 2) H (V × V)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v w : V), ρ (g : H) (v,w) =
      ((e g).1.val.mulVec v,(e g).2.val.mulVec w))
    (f : Additive U →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (f v))
    (hY : offenderSubgroup (NormalElementaryQuotient.representation U q hq hker) ≤ L)
    (hexchange : ∃ t ∈ (T : Subgroup G),
      ((((⊤ : Subgroup D).prod ⊥).map (L.subtype.comp e.symm.toMonoidHom)).map
        (MulAut.conj (q t)).toMonoidHom =
          ((⊥ : Subgroup D).prod ⊤).map (L.subtype.comp e.symm.toMonoidHom)) ∧
      ((((⊥ : Subgroup D).prod ⊤).map (L.subtype.comp e.symm.toMonoidHom)).map
        (MulAut.conj (q t)).toMonoidHom =
          ((⊤ : Subgroup D).prod ⊥).map (L.subtype.comp e.symm.toMonoidHom))) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ L ∧
      (baumann (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ L) ∧
    fixedSpace (NormalElementaryQuotient.representation U q hq hker)
      ((elementaryAbelianMaxJ (T : Subgroup G)).map q) =
      (fixedSpace ρ ((elementaryAbelianMaxJ (T : Subgroup G)).map q)).comap f := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let η : D × D →* H := L.subtype.comp e.symm.toMonoidHom
  have hη : Function.Injective η := L.subtype_injective.comp e.symm.injective
  let JT := elementaryAbelianMaxJ (T : Subgroup G)
  let S := (T : Subgroup G).map q ⊓ L
  have hJTL : JT.map q ≤ L := thompson_image_le_offender_layer T U q hq hker hUT L hY
  have hJTS : JT.map q ≤ S := le_inf (map_mono (sSup_le fun _ h => h.1)) hJTL
  have hnat' (g : L) (v : V × V) : ρ (g : H) v =
      SL2NaturalOffenders.naturalPair (F := F) (e g) v := hnat g v.1 v.2
  have hn : ¬ IsStrongFFModule (ρ.comp L.subtype) :=
    SL2NaturalOffenders.not_strong_of_naturalPair_quotient (ρ.comp L.subtype)
      e.toMonoidHom e.injective (LinearMap.id) Function.surjective_id hnat'
  have hbest (B : Subgroup G) (hB : B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
      (hb : B.map q ≠ ⊥) : IsOffender α (B.map q) :=
    (Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      U q hq hker (T : Subgroup G) B hUT hB hb).isOffender
  have hquot (B : Subgroup G) (hB : B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
      (hb : B.map q ≠ ⊥) : IsOffender ρ (B.map q) :=
    ⟨(hbest B hB hb).1,(fixedCodim_le_of_equivariant_surjection α ρ f hf he _).trans (hbest B hB hb).2⟩
  have hsharp (B : Subgroup G) (hB : B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
      (hb : B.map q ≠ ⊥) : fixedCodim α (B.map q) = fixedCodim ρ (B.map q) := by
    have hBL : B.map q ≤ L := (map_mono (le_sSup hB)).trans hJTL
    have hlow : rank (B.map q) ≤ fixedCodim ρ (B.map q) := by
      apply Nat.le_of_not_gt
      intro hlt
      apply hn
      refine ⟨(B.map q).subgroupOf L,((hquot B hB hb).subgroupOf ρ hBL).1,?_⟩
      rwa [fixedCodim_subgroupOf ρ hBL,rank_subgroupOf hBL]
    exact le_antisymm ((hbest B hB hb).2.trans hlow)
      (fixedCodim_le_of_equivariant_surjection α ρ f hf he _)
  obtain ⟨P,Q,hPQ⟩ := pair_sylow_inf L e (T.mapSurjective hq)
  change S = ((P : Subgroup D).prod Q).map η at hPQ
  have hJT : JT.map q = S := by
    apply le_antisymm hJTS
    have hex : ∃ B ∈ elementaryAbelianMaxSubgroups (T : Subgroup G), B.map q ≠ ⊥ := by
      by_contra! hb
      apply hJ
      rw [←hker]
      exact sSup_le fun B hB => (map_eq_bot_iff B).mp (hb B hB)
    obtain ⟨B,hB,hb⟩ := hex
    have hBL : B.map q ≤ L := (map_mono (le_sSup hB)).trans hJTL
    let B₀ := ((B.map q).subgroupOf L).map e.toMonoidHom
    have hB₀map : B₀.map η = B.map q := by
      change (((B.map q).subgroupOf L).map e.toMonoidHom).map (L.subtype.comp e.symm.toMonoidHom) = _
      rw [Subgroup.map_map]
      have hh : (L.subtype.comp e.symm.toMonoidHom).comp e.toMonoidHom = L.subtype := by
        ext x
        simp
      rw [hh,map_subgroupOf_eq_of_le hBL]
    have hB₀ : IsOffender (SL2NaturalOffenders.naturalPair (F := F)) B₀ :=
      ((hquot B hB hb).subgroupOf ρ hBL).map_equivariant (ρ.comp L.subtype)
        (SL2NaturalOffenders.naturalPair (F := F)) e.toMonoidHom e.injective
        (LinearEquiv.refl (ZMod 2) _) hnat'
    have hB₀le : B₀ ≤ (P : Subgroup D).prod Q := by
      intro x hx
      have hh : η x ∈ S := hJTS (map_mono (le_sSup hB) (hB₀map ▸ mem_map_of_mem η hx))
      rw [hPQ] at hh
      obtain ⟨y,hy,hxy⟩ := hh
      exact hη hxy ▸ hy
    have haxis := pair_offender_contains_axis P Q B₀ hB₀ hB₀le
    obtain ⟨t,ht,hK₁,hK₂⟩ := hexchange
    have hTmap : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    have hJTmap : JT.map (MulAut.conj t).toMonoidHom = JT := by
      exact (elementaryAbelianMaxJ_map_equiv (MulAut.conj t) (T : Subgroup G)).symm.trans
        (congrArg elementaryAbelianMaxJ hTmap)
    have hqconj : (MulAut.conj (q t)).toMonoidHom.comp q = q.comp (MulAut.conj t).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply]
    have hJn : (JT.map q).map (MulAut.conj (q t)).toMonoidHom = JT.map q := by
      rw [Subgroup.map_map,hqconj,←Subgroup.map_map,hJTmap]
    have hSn : S.map (MulAut.conj (q t)).toMonoidHom = S := by
      have hTqn : ((T : Subgroup G).map q).map (MulAut.conj (q t)).toMonoidHom =
          (T : Subgroup G).map q := by
        rw [Subgroup.map_map,hqconj,←Subgroup.map_map,hTmap]
      have hLmap : L.map (MulAut.conj (q t)).toMonoidHom = L :=
        mem_normalizer_iff_map_conj_eq.mp (show q t ∈ normalizer (L : Set H) by
          rw [L.normalizer_eq_top]; trivial)
      exact (Subgroup.map_inf _ _ (MulAut.conj (q t)).toMonoidHom
        (MulAut.conj (q t)).injective).trans (congrArg₂ (· ⊓ ·) hTqn hLmap)
    rw [hPQ]
    apply pair_activation η hη (P : Subgroup D) Q (JT.map q) (MulAut.conj (q t))
      hJn (hPQ ▸ hSn) hK₁ hK₂
    rcases haxis with h | h
    · exact Or.inl ((map_mono h).trans (hB₀map ▸ map_mono (le_sSup hB)))
    · exact Or.inr ((map_mono h).trans (hB₀map ▸ map_mono (le_sSup hB)))
  have hfixedJT := thompson_fixedSpace_of_sharp_maxima T U q hq hker ρ f hf he hsharp
  have hfixed := hfixedJT
  change fixedSpace α (JT.map q) = (fixedSpace ρ (JT.map q)).comap f at hfixed
  rw [hJT] at hfixed
  have hJA' : JT ≤ S.comap q := map_le_iff_le_comap.mp hJT.le
  let E := U ⊓ centralizer (S.comap q : Set G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le (show E ≤ U from inf_le_left)
  have hEalpha : E ≤ thompsonAlpha (T : Subgroup G) :=
    elementary_centralizer_maxJ_le_omegaCenter _ E (inf_le_left.trans hUT)
      (inf_le_right.trans (centralizer_le hJA'))
  refine ⟨⟨hJT,le_antisymm ?_ ?_⟩,hfixedJT⟩
  · rintro _ ⟨a,ha,rfl⟩
    refine ⟨mem_map_of_mem q ha.1,?_⟩
    apply SL2NaturalOffenders.mem_pair_layer_of_fixedSpace L e ρ hfaith hnat P Q
    · obtain ⟨n,hn⟩ := (isPGroup_iff_pow_pow_eq_one.mp T.isPGroup') ⟨a,ha.1⟩
      exact ⟨n,by simpa using congrArg q (congrArg Subtype.val hn)⟩
    · intro v hv
      rw [←hPQ] at hv
      obtain ⟨u,rfl⟩ := hf v
      have hu : u ∈ fixedSpace α S := by rw [hfixed]; exact hv
      have huC : (u.toMul : G) ∈ centralizer (S.comap q : Set G) := by
        apply (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker (S.comap q) u).mp
        rwa [map_comap_eq_self_of_surjective hq]
      have hxu : α (q a) u = u := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change ((NormalElementaryQuotient.representation U q hq hker (q a) u).toMul : G) = u.toMul
        rw [NormalElementaryQuotient.representation_apply]
        rw [←ha.2 u.toMul (hEalpha ⟨u.toMul.property,huC⟩),mul_inv_cancel_right]
      rw [←he,hxu]
  · have hb : JT.map q ≤ (baumann (T : Subgroup G)).map q :=
      map_mono (elementaryAbelianMaxJ_le_baumann _)
    simpa only [hJT] using hb
/-- Image-only form of the paired theorem, retaining the original centralizer quotient. -/
theorem thompson_baumann_images_of_paired_quotient
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hUT : U ≤ T)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (L : Subgroup H) [L.Normal] (e : L ≃* D × D)
    (ρ : Representation (ZMod 2) H (V × V)) (hfaith : Function.Injective ρ)
    (hnat : ∀ (g : L) (v w : V), ρ (g : H) (v,w) =
      ((e g).1.val.mulVec v,(e g).2.val.mulVec w))
    (f : Additive U →ₗ[ZMod 2] (V × V)) (hf : Function.Surjective f)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hker g v) = ρ g (f v))
    (hY : offenderSubgroup (NormalElementaryQuotient.representation U q hq hker) ≤ L)
    (hexchange : ∃ t ∈ (T : Subgroup G),
      ((((⊤ : Subgroup D).prod ⊥).map (L.subtype.comp e.symm.toMonoidHom)).map
        (MulAut.conj (q t)).toMonoidHom =
          ((⊥ : Subgroup D).prod ⊤).map (L.subtype.comp e.symm.toMonoidHom)) ∧
      ((((⊥ : Subgroup D).prod ⊤).map (L.subtype.comp e.symm.toMonoidHom)).map
        (MulAut.conj (q t)).toMonoidHom =
          ((⊤ : Subgroup D).prod ⊥).map (L.subtype.comp e.symm.toMonoidHom))) :
    (elementaryAbelianMaxJ (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ L ∧
      (baumann (T : Subgroup G)).map q = (T : Subgroup G).map q ⊓ L :=
  (paired_images_and_fixedSpace T U q hq hker hUT hJ L e ρ hfaith hnat f hf he hY hexchange).1
end CFSG.Quasithin.ChapterB.RankOneBaumann

