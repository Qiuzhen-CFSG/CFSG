module

public import Stellmacher.SectionTwo.SolvableSL2FrattiniLift
public import Stellmacher.SectionOne.SL2FamilySylowCard
public import Stellmacher.SectionOne.SL2FamilySylowCoordinates
public import Theory.GroupTheory.CenterlessProduct
public import Theory.GroupTheory.SubgroupConjugation

/-!
# A generating `SL₂(2)` coordinate lift for Stellmacher (2.4)

This module supplies the family-wide local-factor construction used in
Stellmacher (2.4), Journal of Algebra 190 (1997), p. 20. Suppose a quotient
image `Ebar` is a nontrivial normal internal product of `SL₂(2)` factors,
its Sylow intersection is the common image `Jbar` of a Sylow subgroup `B₀`
of a normal subgroup `L₀`, and `L₀` together with the ambient Sylow
subgroup generates the whole group. The main theorem finds one subgroup
`K ≤ L₀` containing `B₀` whose Sylow subgroup still maps to `B₀`,
whose quotient first by its 2-core and then by its Frattini subgroup is
`SL₂(2)`, and which itself generates with the ambient Sylow subgroup.

For a factor `D i`, the proof joins `D i` to the Sylow coordinate lines in
all other factors. Direct-product independence identifies the quotient by
those other lines with `D i`. Pulling this coordinate container back inside
`L₀` and applying the Sylow-preserving surjective Frattini-lift theorem
produces an ambient subgroup whose quotient image is the whole container.
The containers cover `Ebar`, so their lifts cover `L₀` modulo the quotient
kernel. An `SL₂(2)` factor makes that kernel joined with the ambient Sylow
subgroup proper. Unique maximality then makes the full lifted family generate,
and a final family selector chooses one generating lift. The companion
theorem retains the selected coordinate and its full quotient image, allowing
the (4.6) and (6.1) consumers to identify the actual action. The original
existence theorem is the projection that discards this additional witness.

The indexed Sylow-coordinate calculation is shared through
`SectionOne.SL2FamilySylowCoordinates`. The private quotient-transport,
Sylow-transport, and maximal-overgroup lemmas stay here because their dependent
subgroup types are tied to this construction. The exported image equation
spells out its coordinate expression, without exposing private definitions. The conclusion deliberately retains the nested Frattini quotient;
it does not assert the generally false stronger quotient by the 2-core alone.
-/

namespace Stellmacher.SectionTwo

universe u

private theorem sl2_family_sylow_coordinates'
    {G : Type u} [Group G] [Finite G]
    (T : Sylow 2 G) (E : Subgroup G) (hEnormal : E.Normal)
    {n : ℕ} (D : Fin n → Subgroup G)
    (hprod : IsInternalDirectProductFamily E D)
    (hSL : ∀ i, IsSL2Two (D i)) :
    ((T : Subgroup G) ⊓ E) = ⨆ i, (T : Subgroup G) ⊓ D i ∧
      ∀ i, Nat.card (↑((T : Subgroup G) ⊓ D i)) = 2 :=
  SectionOne.sl2_family_sylow_coordinates T E hEnormal D hprod hSL

private theorem coordinate_quotient_isSL2Two
    {G : Type u} [Group G] [Finite G]
    (D Q : Subgroup G) (hDQ : D ≤ Subgroup.normalizer (Q : Set G))
    (hdisj : Disjoint D Q) (hD : IsSL2Two D) :
    let R := D ⊔ Q
    letI : (Q.subgroupOf R).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hDQ
    IsSL2Two (R ⧸ Q.subgroupOf R) := by
  dsimp only
  let _ : (Q.subgroupOf (D ⊔ Q)).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer hDQ
  have hQD : Q.subgroupOf D = ⊥ := by
    exact Subgroup.subgroupOf_eq_bot.mpr hdisj.symm
  let _ : (Q.subgroupOf D).Normal := hQD ▸ inferInstance
  let e₂ : (D ⧸ Q.subgroupOf D) ≃*
      ((D ⊔ Q : Subgroup G) ⧸ Q.subgroupOf (D ⊔ Q)) :=
    QuotientGroup.quotientInfEquivProdNormalizerQuotient D Q hDQ
  let eD : (D ⧸ Q.subgroupOf D) ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hQD).trans
      QuotientGroup.quotientBot
  obtain ⟨eSL⟩ := hD
  exact ⟨e₂.symm.trans (eD.trans eSL)⟩

private noncomputable def otherSylowCoordinates
    {G : Type u} [Group G] {n : ℕ}
    (T : Subgroup G) (D : Fin n → Subgroup G) (i : Fin n) : Subgroup G :=
  ⨆ j, ⨆ (_ : j ≠ i), T ⊓ D j

private noncomputable def coordinateContainer
    {G : Type u} [Group G] {n : ℕ}
    (T : Subgroup G) (D : Fin n → Subgroup G) (i : Fin n) : Subgroup G :=
  D i ⊔ otherSylowCoordinates T D i

private theorem factor_le_normalizer_otherSylowCoordinates
    {G : Type u} [Group G] {n : ℕ}
    (T : Subgroup G) (D : Fin n → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ x : G, x ∈ D i →
      ∀ y : G, y ∈ D j → x * y = y * x)
    (i : Fin n) :
    D i ≤ Subgroup.normalizer (otherSylowCoordinates T D i : Set G) := by
  have hotherCent : otherSylowCoordinates T D i ≤
      Subgroup.centralizer (D i : Set G) := by
    dsimp only [otherSylowCoordinates]
    apply iSup_le
    intro j
    apply iSup_le
    intro hji
    apply inf_le_right.trans
    rw [Subgroup.le_centralizer_iff]
    intro x hx y hy
    exact (hcomm i j (Ne.symm hji) x hx y hy).symm
  exact (Subgroup.le_centralizer_iff.mp hotherCent).trans
    (Subgroup.centralizer_le_normalizer _)

private theorem factor_disjoint_otherSylowCoordinates
    {G : Type u} [Group G] {n : ℕ}
    (T : Subgroup G) (D : Fin n → Subgroup G)
    (hind : iSupIndep D) (i : Fin n) :
    Disjoint (D i) (otherSylowCoordinates T D i) := by
  have hotherLe : otherSylowCoordinates T D i ≤
      ⨆ j, ⨆ (_ : j ≠ i), D j := by
    dsimp only [otherSylowCoordinates]
    refine iSup_le fun j => iSup_le fun hji => ?_
    exact inf_le_right.trans (le_iSup_of_le j (le_iSup_of_le hji le_rfl))
  exact (iSupIndep_def.mp hind i).mono le_rfl hotherLe

private theorem otherSylowCoordinates_le_sylowIntersection
    {G : Type u} [Group G] {n : ℕ}
    (T _E J : Subgroup G) (D : Fin n → Subgroup G)
    (hcoords : J = ⨆ i, T ⊓ D i) (i : Fin n) :
    otherSylowCoordinates T D i ≤ J := by
  rw [hcoords]
  dsimp only [otherSylowCoordinates]
  exact iSup_le fun j => iSup_le fun _ => le_iSup (fun k => T ⊓ D k) j

private theorem sylowIntersection_le_coordinateContainer
    {G : Type u} [Group G] {n : ℕ}
    (T _E J : Subgroup G) (D : Fin n → Subgroup G)
    (hcoords : J = ⨆ i, T ⊓ D i) (i : Fin n) :
    J ≤ coordinateContainer T D i := by
  rw [hcoords]
  apply iSup_le
  intro j
  by_cases hji : j = i
  · subst j
    exact inf_le_right.trans le_sup_left
  · exact (le_iSup_of_le j (le_iSup_of_le hji le_rfl) :
      T ⊓ D j ≤ otherSylowCoordinates T D i) |>.trans le_sup_right

private theorem coordinateContainer_le_product
    {G : Type u} [Group G] {n : ℕ}
    (T E : Subgroup G) (D : Fin n → Subgroup G)
    (hgen : E = ⨆ i, D i) (i : Fin n) :
    coordinateContainer T D i ≤ E := by
  rw [hgen]
  apply sup_le (le_iSup D i)
  dsimp only [otherSylowCoordinates]
  refine iSup_le fun j => iSup_le fun _ => ?_
  exact inf_le_right.trans (le_iSup D j)

private theorem product_le_iSup_coordinateContainer
    {G : Type u} [Group G] {n : ℕ}
    (T E : Subgroup G) (D : Fin n → Subgroup G)
    (hgen : E = ⨆ i, D i) :
    E ≤ ⨆ i, coordinateContainer T D i := by
  rw [hgen]
  exact iSup_le fun i => le_sup_left.trans (le_iSup (coordinateContainer T D) i)

private theorem coordinateContainer_quotient_isSL2Two
    {G : Type u} [Group G] [Finite G] {n : ℕ}
    (T : Subgroup G) (D : Fin n → Subgroup G)
    (hprod : IsInternalDirectProductFamily (⨆ i, D i) D)
    (hSL : ∀ i, IsSL2Two (D i)) (i : Fin n) :
    let Q := otherSylowCoordinates T D i
    let R := coordinateContainer T D i
    letI : (Q.subgroupOf R).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (factor_le_normalizer_otherSylowCoordinates T D hprod.2.2 i)
    IsSL2Two (R ⧸ Q.subgroupOf R) := by
  dsimp only [coordinateContainer]
  apply coordinate_quotient_isSL2Two
  · exact factor_le_normalizer_otherSylowCoordinates T D hprod.2.2 i
  · have hcomm : Pairwise fun i j => ∀ x y : G,
        x ∈ D i → y ∈ D j → Commute x y := by
      intro a b hab x y hx hy
      exact hprod.2.2 a b hab x hx y hy
    have hind : iSupIndep D :=
      Subgroup.iSupIndep_of_centerless_of_pairwise_commute D
        (fun j =>
          Stellmacher.SectionOne.RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two
            (hSL j)) hcomm
    exact factor_disjoint_otherSylowCoordinates T D hind i
  · exact hSL i

private theorem nonempty_index_of_nontrivial_sylowIntersection
    {G : Type u} [Group G] {n : ℕ}
    (T E J : Subgroup G) (D : Fin n → Subgroup G)
    (hgen : E = ⨆ i, D i) (hJ : J = T ⊓ E) (hJne : J ≠ ⊥) :
    Nonempty (Fin n) := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hEbot : E = ⊥ := by
      rw [hgen]
      simp
    apply hJne
    simp [hJ, hEbot]
  exact ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩

private theorem le_unique_maximal_ambient
    {G : Type u} [Group G] [Finite G]
    {S K : Subgroup G} {M : Subgroup (⊤ : Subgroup G)}
    (huniq : ∀ M' : Subgroup (⊤ : Subgroup G), IsCoatom M' →
      S ≤ M'.map (⊤ : Subgroup G).subtype → M' = M)
    (hSK : S ≤ K) (hKne : K ≠ ⊤) :
    K ≤ M.map (⊤ : Subgroup G).subtype := by
  let _ : Finite (⊤ : Subgroup G) := Subtype.finite
  have hKsub_ne : K.subgroupOf (⊤ : Subgroup G) ≠ ⊤ := by
    intro htop
    apply hKne
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (show K ≤ (⊤ : Subgroup G) from le_top), htop,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨M', hM'coat, hKM'⟩ :=
    (eq_top_or_exists_le_coatom (K.subgroupOf (⊤ : Subgroup G))).resolve_left hKsub_ne
  have hSM' : S ≤ M'.map (⊤ : Subgroup G).subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le
      (show K ≤ (⊤ : Subgroup G) from le_top)] at hSK
    exact hSK.trans (Subgroup.map_mono hKM')
  rw [← huniq M' hM'coat hSM']
  rw [← Subgroup.map_subgroupOf_eq_of_le
    (show K ≤ (⊤ : Subgroup G) from le_top)]
  exact Subgroup.map_mono hKM'

private theorem eq_top_of_map_eq_top_of_kernel_sup_ne_top
    {G : Type u} [Group G] [Finite G]
    {Q : Type*} [Group Q]
    (S H : Subgroup G) (q : G →* Q)
    (hunique : IsUniqueMaximalContaining S (⊤ : Subgroup G))
    (hSH : S ≤ H) (hkernel : q.ker ⊔ S ≠ ⊤)
    (hmap : H.map q = ⊤) : H = ⊤ := by
  classical
  obtain ⟨M, _hMcoat, _hSM, huniq⟩ := hunique
  by_contra hHne
  have hHM : H ≤ M.map (⊤ : Subgroup G).subtype :=
    le_unique_maximal_ambient huniq hSH hHne
  have hkernelM : q.ker ⊔ S ≤ M.map (⊤ : Subgroup G).subtype :=
    le_unique_maximal_ambient huniq le_sup_right hkernel
  have hsup : H ⊔ q.ker = ⊤ := by
    calc
      H ⊔ q.ker = (H.map q).comap q := (Subgroup.comap_map_eq q H).symm
      _ = ⊤ := by rw [hmap, Subgroup.comap_top]
  have htop : (⊤ : Subgroup G) ≤ M.map (⊤ : Subgroup G).subtype := by
    calc
      (⊤ : Subgroup G) = H ⊔ q.ker := hsup.symm
      _ ≤ M.map (⊤ : Subgroup G).subtype :=
        sup_le hHM (le_sup_left.trans hkernelM)
  have hMtop : M = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    apply le_antisymm
    · exact Subgroup.map_mono le_top
    · simpa [← MonoidHom.range_eq_map, Subgroup.range_subtype] using htop
  exact _hMcoat.1 hMtop

private theorem exists_member_sup_eq_top_of_iSup_sup_eq_top
    {G : Type u} [Group G] [Finite G]
    {I : Type*} [Nonempty I]
    (S : Subgroup G) (K : I → Subgroup G)
    (hunique : IsUniqueMaximalContaining S (⊤ : Subgroup G))
    (hgen : (⨆ i, K i) ⊔ S = ⊤) :
    ∃ i, K i ⊔ S = ⊤ := by
  classical
  obtain ⟨M, hMcoat, hSM, huniq⟩ := hunique
  by_contra hex
  have hproper (i : I) : K i ⊔ S ≠ ⊤ := fun hi ↦ hex ⟨i, hi⟩
  have hKi (i : I) : K i ⊔ S ≤ M.map (⊤ : Subgroup G).subtype :=
    le_unique_maximal_ambient huniq le_sup_right (hproper i)
  have hjoin : (⨆ i, K i) ⊔ S ≤ M.map (⊤ : Subgroup G).subtype := by
    apply sup_le
    · exact iSup_le fun i ↦ le_sup_left.trans (hKi i)
    · exact hSM
  have htop : (⊤ : Subgroup G) ≤ M.map (⊤ : Subgroup G).subtype := by
    rwa [hgen] at hjoin
  have hMtop : M = ⊤ := by
    apply Subgroup.map_subtype_inj.mp
    apply le_antisymm
    · exact Subgroup.map_mono le_top
    · simpa [← MonoidHom.range_eq_map, Subgroup.range_subtype] using htop
  exact hMcoat.1 hMtop

private theorem kernel_sup_sylow_ne_top_of_sl2Two_subgroup
    {G : Type u} [Group G] [Finite G]
    {Q : Type*} [Group Q] [Finite Q]
    (S : Sylow 2 G) (q : G →* Q) (D : Subgroup Q)
    (hDle : D ≤ q.range) (hD : IsSL2Two D) :
    q.ker ⊔ (S : Subgroup G) ≠ ⊤ := by
  intro htop
  have hkerMap : q.ker.map q = ⊥ :=
    (Subgroup.map_eq_bot_iff (f := q) (H := q.ker)).2 le_rfl
  have hmapped := congrArg (fun K : Subgroup G ↦ K.map q) htop
  rw [Subgroup.map_sup, hkerMap, bot_sup_eq] at hmapped
  have hSrange : (S : Subgroup G).map q = q.range :=
    hmapped.trans (MonoidHom.range_eq_map q).symm
  have hDp : IsPGroup 2 D := by
    apply (S.isPGroup'.map q).to_le
    rwa [hSrange]
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hDp
  have hthree : 3 ∣ 2 ^ m := by
    rw [← hm,
      Stellmacher.SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hD]
    norm_num
  have : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hthree
  norm_num at this

private theorem frattini_map_iso
    {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr
      (frattini_le_comap_frattini_of_surjective e.surjective)
  · intro b hb
    have hpre : e.symm b ∈ frattini A :=
      frattini_le_comap_frattini_of_surjective
        (φ := e.symm.toMonoidHom) e.symm.surjective hb
    exact ⟨e.symm b, hpre, e.apply_symm_apply b⟩

private theorem isSL2Two_nested_pCore_frattini_of_mulEquiv
    {A : Type*} {B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B)
    (hA : IsSL2Two
      ((A ⧸ pCore 2 A) ⧸ frattini (A ⧸ pCore 2 A))) :
    IsSL2Two
      ((B ⧸ pCore 2 B) ⧸ frattini (B ⧸ pCore 2 B)) := by
  let eCore : (A ⧸ pCore 2 A) ≃* (B ⧸ pCore 2 B) :=
    QuotientGroup.congr (pCore 2 A) (pCore 2 B) e
      (pCore_map_iso 2 e)
  have hPhi :
      (frattini (A ⧸ pCore 2 A)).map eCore.toMonoidHom =
        frattini (B ⧸ pCore 2 B) :=
    frattini_map_iso eCore
  let ePhi :
      ((A ⧸ pCore 2 A) ⧸ frattini (A ⧸ pCore 2 A)) ≃*
        ((B ⧸ pCore 2 B) ⧸ frattini (B ⧸ pCore 2 B)) :=
    QuotientGroup.congr
      (frattini (A ⧸ pCore 2 A)) (frattini (B ⧸ pCore 2 B))
      eCore hPhi
  obtain ⟨eSL⟩ := hA
  exact ⟨ePhi.symm.trans eSL⟩

private theorem exists_ambient_sylow_of_subgroup_lift
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (P : Sylow 2 H) (K : Subgroup H)
    (hPK : (P : Subgroup H) ≤ K) :
    let Kamb := K.map H.subtype
    ∃ Pamb : Sylow 2 Kamb,
      Pamb.map Kamb.subtype = (P : Subgroup H).map H.subtype := by
  let Kamb : Subgroup G := K.map H.subtype
  let e : K ≃* Kamb :=
    K.equivMapOfInjective H.subtype H.subtype_injective
  let PK : Sylow 2 K := P.subtype hPK
  let Pamb : Sylow 2 Kamb :=
    PK.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨Pamb, ?_⟩
  change ((PK : Subgroup K).map e.toMonoidHom).map Kamb.subtype =
    (P : Subgroup H).map H.subtype
  rw [Subgroup.map_map]
  have he : Kamb.subtype.comp e.toMonoidHom =
      H.subtype.comp K.subtype := by
    ext x
    rfl
  rw [he, ← Subgroup.map_map]
  change (((P.subtype hPK : Sylow 2 K) : Subgroup K).map K.subtype).map
      H.subtype = (P : Subgroup H).map H.subtype
  rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPK]

private theorem exists_coordinate_lift_with_full_image
    {G : Type u} [Group G] [Finite G]
    {barG : Type*} [Group barG] [Finite barG]
    (hsolv : Group.IsSolvable G)
    (q : G →* barG) (Jbar R Qother : Subgroup barG)
    (B₀ L₀ : Subgroup G) (P : Sylow 2 L₀)
    (hPmap : P.map L₀.subtype = B₀)
    (hBmap : B₀.map q = Jbar)
    (hJleR : Jbar ≤ R) (hQleJ : Qother ≤ Jbar)
    (hRle : R ≤ L₀.map q) (hQleR : Qother ≤ R)
    (hQRnormal : (Qother.subgroupOf R).Normal)
    (hSL : IsSL2Two (R ⧸ Qother.subgroupOf R)) :
    ∃ (K : Subgroup G) (PK : Sylow 2 K),
      B₀ ≤ K ∧ K ≤ L₀ ∧ PK.map K.subtype = B₀ ∧
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) ∧
      K.map q = R := by
  classical
  let _ : Group.IsSolvable G := hsolv
  let qL : L₀ →* barG := q.comp L₀.subtype
  let H : Subgroup L₀ := R.comap qL
  have hPH : (P : Subgroup L₀) ≤ H := by
    intro x hx
    change q ((x : L₀) : G) ∈ R
    have hxB : ((x : L₀) : G) ∈ B₀ := by
      rw [← hPmap]
      exact Subgroup.mem_map_of_mem L₀.subtype hx
    have hxJ : q ((x : L₀) : G) ∈ Jbar := by
      rw [← hBmap]
      exact Subgroup.mem_map_of_mem q hxB
    exact hJleR hxJ
  let PH : Sylow 2 H := P.subtype hPH
  let r : H →* R := qL.subgroupComap R
  have hr : Function.Surjective r := by
    intro y
    have hyL : (y : barG) ∈ L₀.map q := hRle y.property
    obtain ⟨g, hgL, hgy⟩ := hyL
    let x : L₀ := ⟨g, hgL⟩
    have hxH : x ∈ H := by
      change q g ∈ R
      rw [hgy]
      exact y.property
    refine ⟨⟨x, hxH⟩, ?_⟩
    exact Subtype.ext hgy
  let _ : (Qother.subgroupOf R).Normal := hQRnormal
  let pi : R →* R ⧸ Qother.subgroupOf R :=
    QuotientGroup.mk' (Qother.subgroupOf R)
  let f : H →* R ⧸ Qother.subgroupOf R := pi.comp r
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective (Qother.subgroupOf R)).comp hr
  obtain ⟨K₀, hPK₀, hK₀map, hK₀SL⟩ :=
    exists_sylow_overgroup_with_sl2Frattini_quotient_and_map_eq_top
      (H := H) (D := R ⧸ Qother.subgroupOf R) inferInstance PH f hf hSL
  let KL : Subgroup L₀ := K₀.map H.subtype
  let K : Subgroup G := KL.map L₀.subtype
  have hPHmapL : (PH : Subgroup H).map H.subtype = (P : Subgroup L₀) := by
    change (((P.subtype hPH : Sylow 2 H) : Subgroup H).map H.subtype) =
      (P : Subgroup L₀)
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hPH]
  have hPKL : (P : Subgroup L₀) ≤ KL := by
    rw [← hPHmapL]
    exact Subgroup.map_mono hPK₀
  have hBK : B₀ ≤ K := by
    rw [← hPmap]
    exact Subgroup.map_mono hPKL
  have hKL : K ≤ L₀ := by
    exact Subgroup.map_subtype_le KL
  have hKr : K₀.map r ≤ (⊤ : Subgroup R) := le_top
  have hKrmap : (K₀.map r).map pi = ⊤ := by
    rw [Subgroup.map_map]
    exact hK₀map
  have hsup : pi.ker ⊔ K₀.map r = ⊤ := by
    rw [sup_comm]
    calc
      K₀.map r ⊔ pi.ker = ((K₀.map r).map pi).comap pi :=
        (Subgroup.comap_map_eq pi (K₀.map r)).symm
      _ = ⊤ := by rw [hKrmap, Subgroup.comap_top]
  have hmapped := congrArg
    (fun U : Subgroup R ↦ U.map R.subtype) hsup
  have hQR : Qother ⊔ (K₀.map r).map R.subtype = R := by
    simpa only [Subgroup.map_sup, pi, QuotientGroup.ker_mk',
      Subgroup.map_subgroupOf_eq_of_le hQleR,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hmapped
  have hKq : K.map q = (K₀.map r).map R.subtype := by
    dsimp only [K, KL]
    rw [Subgroup.map_map, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hQKq : Qother ≤ K.map q := by
    exact hQleJ.trans (hBmap ▸ Subgroup.map_mono hBK)
  have hRq : R ≤ K.map q := by
    calc
      R = Qother ⊔ (K₀.map r).map R.subtype := hQR.symm
      _ ≤ K.map q := sup_le hQKq hKq.ge
  have hqR : K.map q ≤ R := by
    rw [hKq]
    exact Subgroup.map_subtype_le _
  have hKqeq : K.map q = R := le_antisymm hqR hRq
  let eKL : K₀ ≃* KL :=
    K₀.equivMapOfInjective H.subtype H.subtype_injective
  let eK : KL ≃* K :=
    KL.equivMapOfInjective L₀.subtype L₀.subtype_injective
  have hKSL :
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) :=
    isSL2Two_nested_pCore_frattini_of_mulEquiv (eKL.trans eK) hK₀SL
  obtain ⟨PK, hPKmap⟩ :=
    exists_ambient_sylow_of_subgroup_lift L₀ P KL hPKL
  exact ⟨K, PK, hBK, hKL, hPKmap.trans hPmap, hKSL, hKqeq⟩

/-- A generating Frattini lift retaining its selected coordinate and full
quotient image. This supplies the actual action input for (4.6) and (6.1). -/
public theorem exists_generating_coordinate_frattini_lift_with_image
    {G : Type u} [Group G] [Finite G]
    {barG : Type*} [Group barG] [Finite barG]
    (hsolv : Group.IsSolvable G)
    (S : Sylow 2 G) (T : Sylow 2 barG)
    (q : G →* barG) (hq : Function.Surjective q)
    (Jbar Ebar : Subgroup barG)
    (B₀ L₀ : Subgroup G) (P : Sylow 2 L₀)
    (hPmap : P.map L₀.subtype = B₀)
    (hBmap : B₀.map q = Jbar)
    (hJ : Jbar = (T : Subgroup barG) ⊓ Ebar) (hJne : Jbar ≠ ⊥)
    (hLmap : L₀.map q = Ebar)
    (hgenL : L₀ ⊔ (S : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    (hEnormal : Ebar.Normal)
    {n : ℕ} (D : Fin n → Subgroup barG)
    (hprod : IsInternalDirectProductFamily Ebar D)
    (hSL : ∀ i, IsSL2Two (D i)) :
    ∃ (K : Subgroup G) (PK : Sylow 2 K) (i : Fin n),
      B₀ ≤ K ∧ K ≤ L₀ ∧ PK.map K.subtype = B₀ ∧
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) ∧
      K ⊔ (S : Subgroup G) = ⊤ ∧
      K.map q = D i ⊔ ⨆ j : {j : Fin n // j ≠ i}, (T : Subgroup barG) ⊓ D j := by
  classical
  obtain ⟨hcoords₀, _hcoordCards⟩ :=
    sl2_family_sylow_coordinates' T Ebar hEnormal D hprod hSL
  have hcoords : Jbar = ⨆ i, (T : Subgroup barG) ⊓ D i :=
    hJ.trans hcoords₀
  let _ : Nonempty (Fin n) :=
    nonempty_index_of_nontrivial_sylowIntersection
      (T : Subgroup barG) Ebar Jbar D hprod.1 hJ hJne
  have hlocal (i : Fin n) :
      ∃ (K : Subgroup G) (PK : Sylow 2 K),
        B₀ ≤ K ∧ K ≤ L₀ ∧ PK.map K.subtype = B₀ ∧
        IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) ∧
        K.map q = coordinateContainer (T : Subgroup barG) D i := by
    let Qother := otherSylowCoordinates (T : Subgroup barG) D i
    let R := coordinateContainer (T : Subgroup barG) D i
    have hnorm : (Qother.subgroupOf R).Normal := by
      exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (factor_le_normalizer_otherSylowCoordinates
          (T : Subgroup barG) D hprod.2.2 i)
    have hJleR : Jbar ≤ R :=
      sylowIntersection_le_coordinateContainer
        (T : Subgroup barG) Ebar Jbar D hcoords i
    have hQleJ : Qother ≤ Jbar :=
      otherSylowCoordinates_le_sylowIntersection
        (T : Subgroup barG) Ebar Jbar D hcoords i
    have hRleE : R ≤ Ebar :=
      coordinateContainer_le_product
        (T : Subgroup barG) Ebar D hprod.1 i
    have hRle : R ≤ L₀.map q := by
      rwa [hLmap]
    have hQleR : Qother ≤ R := le_sup_right
    have hprod' :
        IsInternalDirectProductFamily (⨆ j, D j) D := ⟨rfl, hprod.2⟩
    have hquot : IsSL2Two (R ⧸ Qother.subgroupOf R) := by
      exact coordinateContainer_quotient_isSL2Two
        (T : Subgroup barG) D hprod' hSL i
    exact exists_coordinate_lift_with_full_image hsolv q Jbar R Qother
      B₀ L₀ P hPmap hBmap hJleR hQleJ hRle hQleR hnorm hquot
  choose K PK hBK hKL hPKmap hKSL hKmap using hlocal
  have hEcover : Ebar ≤ ⨆ i, coordinateContainer (T : Subgroup barG) D i :=
    product_le_iSup_coordinateContainer
      (T : Subgroup barG) Ebar D hprod.1
  have hLcover : L₀.map q ≤ (⨆ i, K i).map q := by
    calc
      L₀.map q = Ebar := hLmap
      _ ≤ ⨆ i, coordinateContainer (T : Subgroup barG) D i := hEcover
      _ = ⨆ i, (K i).map q := by simp only [hKmap]
      _ = (⨆ i, K i).map q := by rw [Subgroup.map_iSup]
  have hfamilyMap : ((⨆ i, K i) ⊔ (S : Subgroup G)).map q = ⊤ := by
    apply top_unique
    rw [← Subgroup.map_top_of_surjective q hq, ← hgenL,
      Subgroup.map_sup, Subgroup.map_sup]
    exact sup_le (hLcover.trans le_sup_left) le_sup_right
  let i₀ : Fin n := Classical.choice inferInstance
  have hDleRange : D i₀ ≤ q.range := by
    exact (show D i₀ ≤ Ebar by
      rw [hprod.1]
      exact le_iSup D i₀) |>.trans
        (hLmap ▸ (Subgroup.map_le_range q L₀))
  have hkernel : q.ker ⊔ (S : Subgroup G) ≠ ⊤ :=
    kernel_sup_sylow_ne_top_of_sl2Two_subgroup S q (D i₀)
      hDleRange (hSL i₀)
  have hfamilyGen : (⨆ i, K i) ⊔ (S : Subgroup G) = ⊤ :=
    eq_top_of_map_eq_top_of_kernel_sup_ne_top
      (S : Subgroup G) ((⨆ i, K i) ⊔ (S : Subgroup G)) q hunique
      le_sup_right hkernel hfamilyMap
  obtain ⟨i, hi⟩ :=
    exists_member_sup_eq_top_of_iSup_sup_eq_top
      (S : Subgroup G) K hunique hfamilyGen
  refine ⟨K i, PK i, i, hBK i, hKL i, hPKmap i, hKSL i, hi, ?_⟩
  simpa only [coordinateContainer, otherSylowCoordinates, iSup_subtype] using hKmap i

/-- A nontrivial normal product of barred `SL₂(2)` coordinates has a
Sylow-preserving Frattini lift that still generates with the ambient Sylow
subgroup. This is the family-wide coordinate selection in Stellmacher (2.4). -/
public theorem exists_generating_coordinate_frattini_lift
    {G : Type u} [Group G] [Finite G]
    {barG : Type*} [Group barG] [Finite barG]
    (hsolv : Group.IsSolvable G)
    (S : Sylow 2 G) (T : Sylow 2 barG)
    (q : G →* barG) (hq : Function.Surjective q)
    (Jbar Ebar : Subgroup barG)
    (B₀ L₀ : Subgroup G) (P : Sylow 2 L₀)
    (hPmap : P.map L₀.subtype = B₀)
    (hBmap : B₀.map q = Jbar)
    (hJ : Jbar = (T : Subgroup barG) ⊓ Ebar) (hJne : Jbar ≠ ⊥)
    (hLmap : L₀.map q = Ebar)
    (hgenL : L₀ ⊔ (S : Subgroup G) = ⊤)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    (hEnormal : Ebar.Normal)
    {n : ℕ} (D : Fin n → Subgroup barG)
    (hprod : IsInternalDirectProductFamily Ebar D)
    (hSL : ∀ i, IsSL2Two (D i)) :
    ∃ (K : Subgroup G) (PK : Sylow 2 K),
      B₀ ≤ K ∧ K ≤ L₀ ∧ PK.map K.subtype = B₀ ∧
      IsSL2Two ((K ⧸ pCore 2 K) ⧸ frattini (K ⧸ pCore 2 K)) ∧
      K ⊔ (S : Subgroup G) = ⊤ := by
  obtain ⟨K, PK, _i, hBK, hKL, hPKmap, hKSL, hgen, _himage⟩ :=
    exists_generating_coordinate_frattini_lift_with_image hsolv S T q hq
      Jbar Ebar B₀ L₀ P hPmap hBmap hJ hJne hLmap hgenL hunique hEnormal D hprod hSL
  exact ⟨K, PK, hBK, hKL, hPKmap, hKSL, hgen⟩

end Stellmacher.SectionTwo
