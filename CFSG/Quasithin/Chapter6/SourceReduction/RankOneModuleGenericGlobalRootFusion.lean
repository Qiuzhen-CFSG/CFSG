module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalTrialityCentralizers
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugateSpan

/-!
# Ambient root TI geometry for the G₂ and triality completions

A central involution is constructed in the actual right factor K = O²(H)
using its concrete core-center model. The established right-parabolic orbit
makes every nonidentity element of Z(K) an involution. If an ambient
conjugator returns a nonidentity point to Z(K), comparison with that orbit
puts its difference in the full point centralizer, hence in N_G(K).
Thus Z(K) is elementary abelian and TI, and N_G(Z(K)) = N_G(K).

I.6.2 then shows that two conjugates of Z(K) centralizing a nonidentity
point of a third conjugate centralize that whole conjugate. This is the
root-pair input to the special-core nonfusion argument in F.4.35. Both
G₂ and genuine graph-field triality applications retain the literal source
S, whole overlap, and original compatible maps. The Chapter12 companion
applies these results to the original chosen-module setup.

Preparation still contains original left uniqueness, and the compatible
comparison is explicit. Exhaustive F.1.12 comparison, involution nonfusion,
and concrete and ambient completion recognition remain to be proved.
Source: Aschbacher–Smith F.4.34–35, printed pp.291–292; 5.3.3, p.659
(`refs/quasithin.pdf`). The imported root calculations retain their existing
source references and ATLAS license attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem center_involution_of_model
    {X : Type*} [Group X] [Finite X] {K : Subgroup G} (e : K ≃* X)
    (hc : (center (pCore 2 X)).map (pCore 2 X).subtype ≤ center X)
    (hd : 2 ∣ Nat.card (center (pCore 2 X))) :
    ∃ z ∈ (center K).map K.subtype, orderOf z = 2 := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := center (pCore 2 X)) 2 hd
  let x : center X := ⟨a.val.val,hc (mem_map_of_mem _ a.property)⟩
  let k := (centerCongr e).symm x
  refine ⟨k.val.val,mem_map_of_mem _ k.property,?_⟩
  have hk : orderOf k = orderOf x := ((centerCongr e).symm).orderOf_eq x
  calc
    orderOf k.val.val = orderOf k := by simp only [Subgroup.orderOf_coe]
    _ = orderOf x := hk
    _ = orderOf a := by
      rw [← Subgroup.orderOf_coe x, ← Subgroup.orderOf_coe a,
        ← Subgroup.orderOf_coe a.val]
    _ = 2 := ha

omit [Finite G] in
private theorem center_orbit_return
    {K P : Subgroup G} (hPN : P ≤ normalizer (K : Set G))
    (hz : ∃ z ∈ (center K).map K.subtype, orderOf z = 2)
    (horbit : ∀ x ∈ (center K).map K.subtype, x ≠ 1 →
      ∀ y ∈ (center K).map K.subtype, y ≠ 1 → ∃ g ∈ P, y = g*x*g⁻¹)
    (hc : ∀ z ∈ (center K).map K.subtype, orderOf z = 2 →
      centralizer ({z} : Set G) ≤ normalizer (K : Set G)) :
    (∀ x ∈ (center K).map K.subtype, x ≠ 1 → orderOf x = 2) ∧
    (∀ g x : G, x ∈ (center K).map K.subtype → x ≠ 1 →
      g*x*g⁻¹ ∈ (center K).map K.subtype → g ∈ normalizer (K : Set G)) := by
  obtain ⟨z,hz,hz2⟩ := hz
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  have hall (x : G) (hx : x ∈ (center K).map K.subtype) (hx1 : x ≠ 1) :
      orderOf x = 2 := by
    obtain ⟨g,hg,he⟩ := horbit z hz hz1 x hx hx1
    rw [he]
    exact ((MulAut.conj g).orderOf_eq z).trans hz2
  refine ⟨hall,?_⟩
  intro g x hx hx1 hgx
  have hgx1 : g*x*g⁻¹ ≠ 1 := by
    exact fun he => hx1 ((MulAut.conj g).map_eq_one_iff.mp he)
  obtain ⟨p,hp,he⟩ := horbit x hx hx1 (g*x*g⁻¹) hgx hgx1
  have hpc : p⁻¹*g ∈ centralizer ({x} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun t : G => p⁻¹*t*g) he
    simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right, inv_mul_cancel, mul_one] using hh
  have hm := (normalizer (K : Set G)).mul_mem (hPN hp) (hc x hx (hall x hx hx1) hpc)
  simpa only [mul_inv_cancel_left] using hm

omit [Finite G] in
/-- The source right center has exponent two, is TI, and has exactly the
original factor normalizer. -/
theorem center_orbit_fusion
    {K P : Subgroup G} (hPN : P ≤ normalizer (K : Set G))
    (hz : ∃ z ∈ (center K).map K.subtype, orderOf z = 2)
    (horbit : ∀ x ∈ (center K).map K.subtype, x ≠ 1 →
      ∀ y ∈ (center K).map K.subtype, y ≠ 1 → ∃ g ∈ P, y = g*x*g⁻¹)
    (hc : ∀ z ∈ (center K).map K.subtype, orderOf z = 2 →
      centralizer ({z} : Set G) ≤ normalizer (K : Set G)) :
    IsElementaryAbelian 2 ((center K).map K.subtype) ∧
    IsTISubgroup ((center K).map K.subtype) ∧
    normalizer (((center K).map K.subtype : Subgroup G) : Set G) =
      normalizer (K : Set G) := by
  obtain ⟨hall,hreturn⟩ := center_orbit_return hPN hz horbit hc
  have hn : normalizer (K : Set G) ≤
      normalizer (((center K).map K.subtype : Subgroup G) : Set G) :=
    normalizer_le_normalizer_characteristic_image K (center K)
  refine ⟨?_,?_,?_⟩
  · refine { toIsMulCommutative := Subgroup.map_isMulCommutative (center K) K.subtype
             exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    apply Subtype.ext
    by_cases hx : (x : G) = 1
    · simp [hx]
    · exact (orderOf_eq_prime_iff.mp (hall x x.property hx)).1
  · apply (isTISubgroup_iff _).mpr
    intro g hg x hx hgx
    by_contra hx1
    exact hg (hn (hreturn g x hx hx1 hgx))
  · apply le_antisymm ?_ hn
    obtain ⟨z,hz,hz2⟩ := hz
    have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
    intro g hg
    exact hreturn g z hz hz1 ((mem_normalizer_iff.mp hg z).mp hz)

/-- The I.6.2 step used in F.4.35: two conjugates of the elementary TI
center which centralize one nonidentity point of a third conjugate centralize
that whole third conjugate. -/
theorem center_conjugate_pair {K : Subgroup G}
    [IsElementaryAbelian 2 ((center K).map K.subtype)]
    (hTI : IsTISubgroup ((center K).map K.subtype))
    (g r s a : G)
    (ha : a ∈ ((center K).map K.subtype).map (MulAut.conj g).toMonoidHom)
    (ha1 : a ≠ 1)
    (hr : ((center K).map K.subtype).map (MulAut.conj r).toMonoidHom ≤
      centralizer ({a} : Set G))
    (hs : ((center K).map K.subtype).map (MulAut.conj s).toMonoidHom ≤
      centralizer ({a} : Set G)) :
    ((center K).map K.subtype).map (MulAut.conj r).toMonoidHom ⊔
      ((center K).map K.subtype).map (MulAut.conj s).toMonoidHom ≤
      centralizer (((((center K).map K.subtype).map (MulAut.conj g).toMonoidHom) :
        Subgroup G) : Set G) := by
  let Z := (center K).map K.subtype
  have hsingle (t : G)
      (ht : Z.map (MulAut.conj t).toMonoidHom ≤ centralizer ({a} : Set G)) :
      Z.map (MulAut.conj t).toMonoidHom ≤
        centralizer (Z.map (MulAut.conj g).toMonoidHom : Set G) := by
    let E := Z.map (MulAut.conj t).toMonoidHom
    let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
    have he : E.map (MulAut.conj (g*t⁻¹)).toMonoidHom =
        Z.map (MulAut.conj g).toMonoidHom := by
      change (Z.conjBy t).conjBy (g*t⁻¹) = Z.conjBy g
      rw [←conjBy_mul]
      simp only [inv_mul_cancel_right]
    have hac : a ∈ centralizer (E : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mp (ht hx)
    have hh := (hTI.map_equiv (MulAut.conj t)).conjugate_le_centralizer_of_point
      (g*t⁻¹) a (he.symm ▸ ha) ha1 hac
    rw [he] at hh
    exact le_centralizer_iff.mp hh
  exact sup_le (hsingle r hr) (hsingle s hs)

/-- In the actual G₂ comparison, the right factor's center is elementary,
TI, and has full normalizer N_G(K). -/
theorem Preparation.g2_right_center_fusion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    IsElementaryAbelian 2 ((center (residual H)).map (residual H).subtype) ∧
    IsTISubgroup ((center (residual H)).map (residual H).subtype) ∧
    normalizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) =
      normalizer (residual H : Set G) := by
  have hs := d.g2_local_structure h hH.1.1.2 hp F he
  obtain ⟨e⟩ := hs.2.2.1
  have hd : 2 ∣ Nat.card (center (pCore 2 (Atlas.G2.LieParabolicSetup.local₁ (F := F)))) := by
    rw [Atlas.G2.LieParabolicSetup.local₁_pCore_special.2.2.2.2.2.2,hs.1]
    exact dvd_pow_self 2 (by have := h.exponent; omega : n ≠ 0)
  have hz := center_involution_of_model e
    Atlas.G2.LieParabolicSetup.local₁_core_center_le_center hd
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  exact center_orbit_fusion hPN hz (d.g2_right_center_orbit h hH.1.1.2 hp F he)
    (d.g2_central_involution_centralizers h hH hp F he 1)

/-- F.4.34 for the genuine triality comparison, with its literal right center. -/
theorem Preparation.triality_right_center_fusion
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 0 < m)
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.Triality.amalgam
          (_root_.Triality.Standard.binaryParameters m hm)).reverse)) :
    IsElementaryAbelian 2 ((center (residual H)).map (residual H).subtype) ∧
    IsTISubgroup ((center (residual H)).map (residual H).subtype) ∧
    normalizer (((center (residual H)).map (residual H).subtype : Subgroup G) : Set G) =
      normalizer (residual H : Set G) := by
  have horbit := d.triality_right_center_orbit h hH.1.1.2 hp m hm he
  have hcentral := d.triality_central_involution_centralizers h hH hp m hm he 1
  rcases he with he | he
  · exact (d.not_triality_arms_left_amalgam h hH.1.1.2 hp
      (_root_.Triality.Standard.binaryParameters m hm) rfl he).elim
  obtain ⟨e⟩ := he
  obtain ⟨a⟩ := (d.triality_factor_equivs h hH.1.1.2 hp m hm e).2
  have hd : 2 ∣ Nat.card (center (pCore 2
      (_root_.Triality.Standard.Parabolics.localFactor
        (_root_.Triality.Standard.binaryParameters m hm) .arms))) := by
    rw [_root_.Triality.Standard.Parabolics.localFactor_arms_twoCore_center_card _ rfl]
    change 2 ∣ 2^m
    exact dvd_pow_self 2 (by omega : m ≠ 0)
  have hz := center_involution_of_model a
    (_root_.Triality.Standard.Parabolics.arms_core_center_le_center _ rfl) hd
  have hPN : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ≤
      normalizer (residual H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 from
        le_sup_left.trans le_sup_left)).mp ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 1)
  exact center_orbit_fusion hPN hz horbit hcentral

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
