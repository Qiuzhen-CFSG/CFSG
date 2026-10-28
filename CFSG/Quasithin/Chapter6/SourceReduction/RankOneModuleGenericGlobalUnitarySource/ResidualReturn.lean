module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourReturn
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.FullStabilizer
public import Theory.GroupTheory.WeakClosurePairFusion
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.FullStabilizer

/-!
# Ambient long-root returns through the original plane residual

Synchronize plane-Sylow and point conjugation through the actual reduced
amalgam, placing an involution in the core in both ambient groups. Ambient
Thompson fusion on that core is induced by an automorphism of L. The
intrinsic native long-root criterion and the matrix rank-one placement
then put every ambient long-root conjugate returning to L in O₂(L).
Transitivity on the original right-residual center makes this assertion
apply to every previously marked long root, without changing witnesses.

For the same short and long roots and entire q-element line, simultaneous
Burnside correction and the known common-centralizer bound put every
residual-return transporter in N_G(L). Lifting through the literal line
quotient proves the corresponding bound for returns to its residual image.
Both orientations, degree-two rows, q=4 and n=2m with m>1 are retained.

Source: Aschbacher–Smith F.4.35 and F.4.42, printed pp.292 and295.
Returns through outer elements of the full stabilizer still require their
source argument. Unique fixed cosets, maximal-W containment, outer transfer
and the same-extension order comparison are not asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour UnitaryCompletion
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneLocal UnitaryFourPlaneRadical UnitaryFourShortRoot
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

private theorem residual_long_return
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] ((T : Subgroup G) ⊓ L)) (amalgam m hm).reverse)
    (f : localFactor (MatrixField m) (form (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm)) ≃* L)
    (hf : ∀ x, ∀ hx : (f x).val ∈
        ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0,
      (e.left ⟨(f x).val,hx⟩).val = projection m hm x.val)
    (x : L) (hx : IsConj
      (f (longLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))).val x.val) :
    x ∈ pCore 2 L := by
  let : NeZero m := ⟨by omega⟩
  let P := ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L)
  let B := localFactor (MatrixField m) (form (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm))
  let z₀ : B := longLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
  have hLP : L ≤ P 0 := le_sup_left.trans le_sup_left
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (fun he => .unitary m hm he) (fun he => .unitaryExtension m hm he))
  have hzcore : z₀ ∈ pCore 2 B := by
    rw [←radical_eq_twoCore]
    exact (radicalEquiv (MatrixField m) (fieldConj m) (fieldConj_involutive m hm)
      (Multiplicative.ofAdd (longParameter (MatrixField m) (fieldConj m)))).property
  have hzQ : (f z₀).val ∈ L.pCoreIn 2 := by
    apply mem_map_of_mem L.subtype
    rw [←pCore_map_iso 2 f]
    exact mem_map_of_mem f.toMonoidHom hzcore
  have hzs : z₀^2=1 := by
    have he := pow_orderOf_eq_one
      (SourceNormalizer.FourShortRoot.longMark (MatrixField m) (fieldConj m)
        (fieldConj_involutive m hm))
    rw [SourceNormalizer.FourShortRoot.longMark_order] at he
    exact congrArg Subtype.val he
  have hxs : (⟨x.val,hLP x.property⟩ : P 0)^2=1 := by
    apply Subtype.ext
    have hs : (f z₀).val^2=1 := by
      simpa only [map_pow,map_one,Subgroup.coe_pow,Subgroup.coe_one] using
        congrArg (fun b : B => (f b).val) hzs
    exact isConj_one_right.mp (hs ▸ hx.pow 2)
  obtain ⟨y,hy,hxy,hxyN⟩ := ChapterF.UnitarySource.FourReturn.synchronized_involution_placement
    m hm (P 0) (P 1) e ⟨x.val,hLP x.property⟩ hxs
  have hyQ : y.val ∈ L.pCoreIn 2 :=
    ChapterF.UnitarySource.FourPlacement.plane_comparison_core_le_residual_core
      m hm (P 0) L e.left (hr 0) (mem_map_of_mem (P 0).subtype hy)
  let yL : L := ⟨y.val,pCoreIn_le 2 L hyQ⟩
  obtain ⟨g,hg,he⟩ := d.unitary_core_fusion h hH hp m hm hc hzQ hyQ (hx.trans hxy)
  let c := L.normalizerMonoidHom ⟨g,hg⟩
  let a : MulAut B := f.trans (c.trans f.symm)
  have ha : a z₀ = f.symm yL := by
    apply f.injective
    change f (f.symm (c (f z₀))) = f (f.symm yL)
    rw [f.apply_symm_apply,f.apply_symm_apply]
    exact Subtype.ext he
  have hn := ChapterF.UnitarySource.FourReturn.automorphism_long m hm a
  change IsConj (projection m hm z₀.val) (projection m hm (a z₀).val) at hn
  rw [ha] at hn
  have hxN : (e.left ⟨x.val,hLP x.property⟩).val = projection m hm (f.symm x).val := by
    have hh := hf (f.symm x) (by rw [f.apply_symm_apply]; exact hLP x.property)
    simpa only [f.apply_symm_apply] using hh
  have hyN : (e.left y).val = projection m hm (f.symm yL).val := by
    have hh := hf (f.symm yL) (by rw [f.apply_symm_apply]; exact y.property)
    simpa only [f.apply_symm_apply] using hh
  rw [hxN,hyN] at hxyN
  have hnative := hn.trans hxyN.symm
  have hmat : IsConj z₀.val (f.symm x).val := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hnative
    obtain ⟨k,hk⟩ := project_surjective (MatrixField m) (standardForm m hm) g
    let u : MatrixGroup m hm := z₀.val
    let v : MatrixGroup m hm := (f.symm x).val
    have heq : k*u*k⁻¹=v := by
      apply projection_injective m hm
      change projection m hm k = g at hk
      have he : projection m hm (k*u*k⁻¹) =
          projection m hm k * projection m hm u * (projection m hm k)⁻¹ :=
        ((projection m hm).map_mul (k*u) k⁻¹).trans
          (congrArg₂ (fun b c => b*c) ((projection m hm).map_mul k u)
            ((projection m hm).map_inv k))
      exact he.trans (by rw [hk]; exact hg)
    exact isConj_iff.mpr ⟨k,heq⟩
  have hxrad := long_conjugate_in_plane_mem_radical (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm) (f.symm x) hmat
  rw [radical_eq_twoCore] at hxrad
  rw [←pCore_map_iso 2 f]
  exact ⟨f.symm x,hxrad,f.apply_symm_apply x⟩


/-- Every ambient conjugate of any nonidentity original right-center
involution returning to L belongs to its two-core. This applies to the
same long root in each previously constructed short-line quotient. -/
theorem Preparation.unitary_long_residual_return
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (z : G) (hz : z ∈ (center (residual H)).map (residual H).subtype)
    (hz2 : orderOf z = 2) (x : L) (hx : IsConj z x.val) : x ∈ pCore 2 L := by
  obtain ⟨hm',_,e,_⟩ := d.unitary_short_root_common_centralizers h hH hp m hm hc
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (fun he => .unitary m hm he) (fun he => .unitaryExtension m hm he))
  obtain ⟨a,ha,_,haz⟩ := ChapterF.UnitarySource.FourShortMarked.marked_plane_equiv_with_map
    (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L))
    L (residual H) hr m hm hm' e
  let z₀ := SourceNormalizer.FourShortRoot.longMark (MatrixField m) (fieldConj m)
    (fieldConj_involutive m hm)
  have hz₀ : (a z₀.val).val ≠ 1 := by
    intro he
    have he' : z₀ = 1 := Subtype.ext (a.injective ((Subtype.ext he).trans (map_one a).symm))
    have ho := SourceNormalizer.FourShortRoot.longMark_order (MatrixField m) (fieldConj m)
      (fieldConj_involutive m hm)
    change orderOf z₀ = 2 at ho
    rw [he',orderOf_one] at ho
    contradiction
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz2
  obtain ⟨g,_,hg⟩ := d.unitary_right_center_orbit h hH.1.1.2 hp m hm hc
    (a z₀.val).val haz hz₀ z hz hz1
  exact residual_long_return d h hH hp m hm hc e a ha x
    ((isConj_iff.mpr ⟨g,hg.symm⟩).trans hx)

private theorem short_core_return_transporter
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (t z : G) (ht : t ∈ L.pCoreIn 2) (hz : z ∈ L.pCoreIn 2)
    (hcommon : centralizer ({t} : Set G) ⊓ centralizer ({z} : Set G) ≤ normalizer (L : Set G))
    (g : G) (hgt : g*t*g⁻¹=t) (hg : g*z*g⁻¹ ∈ L.pCoreIn 2) :
    g ∈ normalizer (L : Set G) := by
  let Q := L.pCoreIn 2
  have hJ := d.unitary_thompson h hH hp m hm hc
  have hQP : Q ≤ (T : Subgroup G) := by
    change L.pCoreIn 2 ≤ (T : Subgroup G)
    rw [←hJ]
    exact sSup_le fun _ hA => hA.1
  have hw : ∀ a : G, Q.map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G) →
      a ∈ normalizer (Q : Set G) := by
    intro a ha
    change (L.pCoreIn 2).map (MulAut.conj a).toMonoidHom ≤ (T : Subgroup G) at ha
    change a ∈ normalizer (L.pCoreIn 2 : Set G)
    rw [←hJ] at ha ⊢
    exact maxJ_weakly_closed T a ha
  have habel : Q ≤ centralizer (Q : Set G) :=
    (d.unitary_core_centralizer h hH hp m hm hc).ge
  obtain ⟨a,ha,haz,hat⟩ := Sylow.PointwiseFusion.pair_fusion T Q hQP hw
    (habel hz) (habel ht) (habel hg) (habel ht) g rfl hgt
  have hn : normalizer (Q : Set G) = normalizer (L : Set G) := by
    change normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G)
    rw [←hJ]
    exact d.unitary_thompson_normalizer h hH hp m hm hc
  have hcorr (x y : G) (hax : a*x*a⁻¹=y) (hgx : g*x*g⁻¹=y) :
      a⁻¹*g ∈ centralizer ({x} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      _ = a⁻¹*(g*x*g⁻¹)*a := by group
      _ = x := by rw [hgx,←hax]; group
  have hb := hcommon ⟨hcorr t t hat hgt,hcorr z (g*z*g⁻¹) haz rfl⟩
  have hmem := (normalizer (L : Set G)).mul_mem (hn ▸ ha) hb
  exact (mul_inv_cancel_left a g) ▸ hmem

/-- Ambient long-root returns through the original residual lie in its
core and are fused by the full short stabilizer. The same assertion in
the literal line quotient retains the entire q-element kernel. -/
theorem Preparation.unitary_short_residual_return
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤ normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      U ≤ V ∧ IsElementaryAbelian 2 V ∧ Nat.card V = (2^m)^3 ∧
      Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      (∀ x : L, IsConj z.val.val x.val → x ∈ pCore 2 L) ∧
      (∀ g : centralizer ({t.val} : Set G), g.val*z.val.val*g.val⁻¹ ∈ L →
        g.val ∈ normalizer (L : Set G) ∧
        ∃ a : centralizer ({t} : Set L),
          a.val.val*z.val.val*a.val.val⁻¹ = g.val*z.val.val*g.val⁻¹) ∧
      (∀ g : UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U,
        g*f z*g⁻¹ ∈ (L.comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
          (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U)) →
        g ∈ UnitarySource.shortLineLocalQuotient L t U) := by
  obtain ⟨hm',hn,e,_,_,_,hcommon⟩ :=
    d.unitary_short_root_common_centralizers h hH hp m hm hc
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (fun he => .unitary m hm he) (fun he => .unitaryExtension m hm he))
  obtain ⟨a,_,hat,haz⟩ := ChapterF.UnitarySource.FourShortMarked.marked_plane_equiv_with_map
    (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L))
    L (residual H) hr m hm hm' e
  let t := a (shortLocal (MatrixField m) (fieldConj m) (fieldConj_involutive m hm))
  obtain ⟨ht,z,hzmark,hz,U,hV,hVQ,hVc,hUc,hindex,hUV,hU,htU,_⟩ :=
    short_quotient_from_marked_equiv m hm hm' a
  have hzc : z.val.val ∈ (center (residual H)).map (residual H).subtype := by
    rw [hzmark]
    exact haz
  have hC : centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤ normalizer (L : Set G) := by
    rw [show t.val = (ChapterF.UnitarySource.FourShortTransport.sourceShort m hm e).val from hat]
    exact hcommon z.val.val hzc hz
  let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
  let f := UnitarySource.shortLineQuotientMap L t U hU
  have hker : f.ker = U := UnitarySource.shortLineQuotientMap_ker L t U hU
  let : IsElementaryAbelian 2 V := hV
  have hcV : Nat.card (V.map f) = (2^m)^2 := by rw [←relIndex_ker,hker]; exact hindex
  have hreturn (x : L) (hx : IsConj z.val.val x.val) : x ∈ pCore 2 L :=
    d.unitary_long_residual_return h hH hp m hm hc z.val.val hzc hz x hx
  have htQ : t.val ∈ L.pCoreIn 2 := hVQ
    (mem_map_of_mem L.subtype (mem_map_of_mem (centralizer ({t} : Set L)).subtype
      (hUV (htU.le (mem_zpowers _)))))
  have hzQ : z.val.val ∈ L.pCoreIn 2 := hVQ
    (mem_map_of_mem L.subtype (mem_map_of_mem (centralizer ({t} : Set L)).subtype
      (subset_normalClosure (Set.mem_singleton _))))
  have htrans (g : centralizer ({t.val} : Set G))
      (hg : g.val*z.val.val*g.val⁻¹ ∈ L) : g.val ∈ normalizer (L : Set G) := by
    apply short_core_return_transporter d h hH hp m hm hc t.val z.val.val htQ hzQ hC g.val
      (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property))
    exact mem_map_of_mem L.subtype (hreturn ⟨_,hg⟩ (isConj_iff.mpr ⟨g.val,rfl⟩))
  refine ⟨hm',hn,t,ht,z,hz,hzc,hC,U,hU,hUV,hV,hVc,hUc,hker,
    IsElementaryAbelian.map f,hcV,htU,hreturn,?_,?_⟩
  · intro g hg
    have hgn := htrans g hg
    refine ⟨hgn,?_⟩
    obtain ⟨b,hb⟩ := UnitarySource.marked_longClass_fusion L m hm hm' a g.val hgn
      (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp g.property))
    refine ⟨b,?_⟩
    rw [hzmark]
    exact hb
  · let K := UnitarySource.shortLineKernel L t U
    let j := UnitarySource.shortLineAmbientEmbedding L t U
    let q := QuotientGroup.mk' K
    let zN := UnitarySource.shortLineNormalizerMap L t U hU z
    have hKL : K.map j ≤ L := by
      rintro _ ⟨b,hb,rfl⟩
      obtain ⟨u,_,he⟩ := hb
      have hh := congrArg (fun x : centralizer ({t.val} : Set G) => x.val) he
      change u.val.val = j b at hh
      exact hh ▸ u.val.property
    intro g hg
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective K g
    obtain ⟨w,hw,he⟩ := hg
    change j w ∈ L at hw
    have hq : q w = q (b*zN*b⁻¹) := by
      change q w = q b * q zN * (q b)⁻¹ at he
      rw [map_mul,map_mul,map_inv]
      exact he
    have hk : w⁻¹*(b*zN*b⁻¹) ∈ K := QuotientGroup.eq.mp hq
    have hmem : j (b*zN*b⁻¹) ∈ L := by
      have hh := L.mul_mem hw (hKL (mem_map_of_mem j hk))
      simpa only [map_mul,map_inv,mul_inv_cancel_left] using hh
    exact (UnitarySource.shortLineLocalQuotient_mk_iff L t U b).mpr (htrans b.val hmem)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
