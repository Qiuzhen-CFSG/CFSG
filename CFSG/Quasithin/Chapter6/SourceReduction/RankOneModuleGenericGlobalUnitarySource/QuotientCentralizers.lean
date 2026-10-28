module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedQuotient

/-!
# Centralizers and transporters in the ambient short-line quotient

Let t and z be the same marked short and long roots, U the entire short
line, and Q=O₂(L). A conjugator in N_{C_G(t)}(U)/U returning the image of z
to the image of Q lifts to a conjugator returning z to Q, since U≤Q.
Burnside correction inside N_{C_G(t)}(U) gives an element normalizing L
with the identical conjugation on z. Their difference centralizes both
original roots; the proved ambient common-centralizer bound therefore
places the original lift in N_G(L).

The residual orbit on the q²-element orthogonal quotient transfers this
to every nonzero vector. Thus their full centralizers, and normalizers of
all nontrivial subgroups of that quotient module, lie in the literal image
of N_{C_G(t)}(U)∩N_G(L). The quotient membership criterion retains the
whole kernel and applies to every lift. The prepared and chosen-module
applications require no additional centralizer or fusion assumptions.

Source: Aschbacher–Smith F.4.42, printed pp.295–296 of
`refs/quasithin.pdf`. These are ambient quotient bounds. The unique-fixed-
coset step still has to handle conjugates returning to the whole local
subgroup, beyond returns to the core image; full F.4.42 is not asserted.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open UnitaryCompletion
namespace UnitarySource
variable {G : Type*} [Group G] (L : Subgroup G) (t : L)

/-- The original normalizer intersected with the ambient short-line normalizer. -/
def shortLineLocal (U : Subgroup (centralizer ({t} : Set L))) :
    Subgroup (shortLineNormalizer L t U) :=
  (normalizer (L : Set G)).comap (shortLineAmbientEmbedding L t U)

/-- Its literal image modulo the entire short-root line. -/
def shortLineLocalQuotient (U : Subgroup (centralizer ({t} : Set L))) :
    Subgroup (shortLineNormalizer L t U ⧸ shortLineKernel L t U) :=
  (shortLineLocal L t U).map (QuotientGroup.mk' (shortLineKernel L t U))

/-- The entire quotient kernel lies in the original local subgroup. -/
theorem shortLineKernel_le_local (U : Subgroup (centralizer ({t} : Set L))) :
    shortLineKernel L t U ≤ shortLineLocal L t U := by
  intro a ha
  obtain ⟨u,hu,he⟩ := ha
  change a.val.val ∈ normalizer (L : Set G)
  have hh := congrArg (fun x : centralizer ({t.val} : Set G) => x.val) he
  change u.val.val = a.val.val at hh
  exact hh ▸ L.le_normalizer u.val.property

/-- The original residual centralizer maps into the quotient local subgroup. -/
theorem shortLineQuotientMap_mem_local (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L))) (a : centralizer ({t} : Set L)) :
    shortLineQuotientMap L t U hU a ∈ shortLineLocalQuotient L t U :=
  mem_map_of_mem _ (L.le_normalizer a.val.property)

/-- Membership in the quotient local subgroup is detected on every lift;
the full line is contained in the local subgroup. -/
theorem shortLineLocalQuotient_mk_iff (U : Subgroup (centralizer ({t} : Set L)))
    (a : shortLineNormalizer L t U) :
    QuotientGroup.mk' (shortLineKernel L t U) a ∈ shortLineLocalQuotient L t U ↔
      a.val.val ∈ normalizer (L : Set G) := by
  constructor
  · rintro ⟨b,hb,he⟩
    have hk : b⁻¹*a ∈ shortLineKernel L t U := QuotientGroup.eq.mp he
    have hh := (shortLineLocal L t U).mul_mem hb (shortLineKernel_le_local L t U hk)
    change b*(b⁻¹*a) ∈ shortLineLocal L t U at hh
    change a ∈ shortLineLocal L t U
    simpa only [mul_inv_cancel_left] using hh
  · intro ha
    exact mem_map_of_mem _ ha

end UnitarySource

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

private theorem short_line_quotient_transporter
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (t : L) (ht : t.val ∈ L.pCoreIn 2)
    (z : centralizer ({t} : Set L)) (hz : z.val.val ∈ L.pCoreIn 2)
    (hcommon : centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
      normalizer (L : Set G))
    (U : Subgroup (centralizer ({t} : Set L)))
    (hU : U ≤ center (centralizer ({t} : Set L)))
    (hUQ : ∀ u ∈ U, u.val.val ∈ L.pCoreIn 2)
    (g : UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U)
    (hg : g * UnitarySource.shortLineQuotientMap L t U hU z * g⁻¹ ∈
      ((L.pCoreIn 2).comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
        (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U))) :
    g ∈ UnitarySource.shortLineLocalQuotient L t U := by
  let Q := L.pCoreIn 2
  let j := UnitarySource.shortLineAmbientEmbedding L t U
  let K := UnitarySource.shortLineKernel L t U
  let q := QuotientGroup.mk' K
  let x := UnitarySource.shortLineNormalizerMap L t U hU z
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
  have hQj : Q ≤ j.range :=
    UnitarySource.core_le_shortLineAmbientEmbedding_range L t U Q habel ht hUQ
  have hKQ : K.map j ≤ Q := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨u,hu,he⟩ := ha
    have hh := congrArg (fun x : centralizer ({t.val} : Set G) => x.val) he
    change u.val.val = j a at hh
    exact hh ▸ hUQ u hu
  obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective K g
  obtain ⟨w,hwQ,he⟩ := hg
  change j w ∈ Q at hwQ
  change q w = q b * q x * (q b)⁻¹ at he
  have heq : q w = q (b*x*b⁻¹) := by
    simpa only [map_mul,map_inv] using he
  have hk : w⁻¹*(b*x*b⁻¹) ∈ K := QuotientGroup.eq.mp heq
  have hy : j (b*x*b⁻¹) ∈ Q := by
    have hh := Q.mul_mem hwQ (hKQ (mem_map_of_mem j hk))
    simpa only [map_mul,map_inv,mul_inv_cancel_left] using hh
  obtain ⟨a,ha,hea⟩ := Sylow.WeakClosure.embedding_fusion T Q hQP hw j
    (UnitarySource.shortLineAmbientEmbedding_injective L t U) hQj
    (habel hz) (habel hy) b rfl
  have hnorm : normalizer (Q : Set G) = normalizer (L : Set G) := by
    change normalizer (L.pCoreIn 2 : Set G) = normalizer (L : Set G)
    rw [←hJ]
    exact d.unitary_thompson_normalizer h hH hp m hm hc
  have haN : j a ∈ normalizer (L : Set G) := hnorm ▸ ha
  have hcomm : j (a⁻¹*b) ∈ centralizer ({z.val.val} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    have he' : j a*z.val.val*(j a)⁻¹ = j b*z.val.val*(j b)⁻¹ := by
      simpa only [map_mul,map_inv,show j x = z.val.val from rfl] using congrArg j hea
    simp only [map_mul,map_inv]
    calc
      _ = (j a)⁻¹*(j b*z.val.val*(j b)⁻¹)*j a := by group
      _ = z.val.val := by rw [←he']; group
  have habN : j (a⁻¹*b) ∈ normalizer (L : Set G) := hcommon ⟨(a⁻¹*b).val.property,hcomm⟩
  have hbN : j b ∈ normalizer (L : Set G) := by
    have hh := (normalizer (L : Set G)).mul_mem haN habN
    simpa only [map_mul,map_inv,mul_inv_cancel_left] using hh
  exact mem_map_of_mem q hbN

/-- The actual ambient line quotient has no additional transporters returning
nonzero orthogonal vectors to the core image. Consequently their full
quotient centralizers, and normalizers of every nontrivial subgroup of the
orthogonal module, lie in the image of the original local normalizer. -/
theorem Preparation.unitary_short_quotient_centralizers
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm) :
    1 < m ∧ n = 2*m ∧
    ∃ t : L, orderOf t.val = 2 ∧
    ∃ z : centralizer ({t} : Set L), orderOf z.val.val = 2 ∧
      z.val.val ∈ (center (residual H)).map (residual H).subtype ∧
      centralizer ({t.val} : Set G) ⊓ centralizer ({z.val.val} : Set G) ≤
        normalizer (L : Set G) ∧
    ∃ U : Subgroup (centralizer ({t} : Set L)),
    ∃ hU : U ≤ center (centralizer ({t} : Set L)),
      let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
      let f := UnitarySource.shortLineQuotientMap L t U hU
      let Q := ((L.pCoreIn 2).comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
        (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U))
      let X := UnitarySource.shortLineLocalQuotient L t U
      U ≤ V ∧ IsElementaryAbelian 2 V ∧
      (V.map (centralizer ({t} : Set L)).subtype).map L.subtype ≤ L.pCoreIn 2 ∧
      Nat.card V = (2^m)^3 ∧ Nat.card U = 2^m ∧ f.ker = U ∧
      IsElementaryAbelian 2 (V.map f) ∧ Nat.card (V.map f) = (2^m)^2 ∧
      zpowers (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) < U ∧
      f (⟨t,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set L)) = 1 ∧
      f z ≠ 1 ∧
      (∀ v ∈ V.map f, v ≠ 1 → ∀ g, g*v*g⁻¹ ∈ Q → g ∈ X) ∧
      (∀ v ∈ V.map f, v ≠ 1 → centralizer ({v} : Set _) ≤ X) ∧
      ∀ P : Subgroup (UnitarySource.shortLineNormalizer L t U ⧸ UnitarySource.shortLineKernel L t U),
        P ≤ V.map f → P ≠ ⊥ → normalizer (P : Set _) ≤ X := by
  obtain ⟨hm',hn,t,ht,z,hz,hzc,hcommon,U,hU,hUV,hV,hVQ,hVc,hUc,hker,
    hVe,hVi,htU,htkill,hzne,horbit,_⟩ :=
    d.unitary_marked_short_quotient_with_line h hH hp m hm hc
  let V := normalClosure ({z} : Set (centralizer ({t} : Set L)))
  let f := UnitarySource.shortLineQuotientMap L t U hU
  let Q := ((L.pCoreIn 2).comap (UnitarySource.shortLineAmbientEmbedding L t U)).map
    (QuotientGroup.mk' (UnitarySource.shortLineKernel L t U))
  let X := UnitarySource.shortLineLocalQuotient L t U
  have hUQ : ∀ u ∈ U, u.val.val ∈ L.pCoreIn 2 := by
    intro u hu
    exact hVQ (mem_map_of_mem L.subtype
      (mem_map_of_mem (centralizer ({t} : Set L)).subtype (hUV hu)))
  have htQ : t.val ∈ L.pCoreIn 2 := hUQ _ (htU.le (mem_zpowers _))
  have hzQ : z.val.val ∈ L.pCoreIn 2 := hVQ (mem_map_of_mem L.subtype
    (mem_map_of_mem (centralizer ({t} : Set L)).subtype
      (subset_normalClosure (Set.mem_singleton _))))
  have hVmap : V.map f ≤ Q := by
    rintro v ⟨w,hw,rfl⟩
    refine ⟨UnitarySource.shortLineNormalizerMap L t U hU w,?_,rfl⟩
    exact hVQ (mem_map_of_mem L.subtype
      (mem_map_of_mem (centralizer ({t} : Set L)).subtype hw))
  have htrans : ∀ v ∈ V.map f, v ≠ 1 → ∀ g, g*v*g⁻¹ ∈ Q → g ∈ X := by
    intro v hv hv1 g hg
    obtain ⟨a,_,he⟩ := horbit v hv hv1
    change f a * f z * (f a)⁻¹ = v at he
    have hga : g * f a ∈ X := by
      apply short_line_quotient_transporter d h hH hp m hm hc t htQ z hzQ hcommon U hU hUQ
      change (g*f a)*f z*(g*f a)⁻¹ ∈ Q
      have hh : (g*f a)*f z*(g*f a)⁻¹ = g*v*g⁻¹ := by rw [←he]; group
      rwa [hh]
    have ha : f a ∈ X := UnitarySource.shortLineQuotientMap_mem_local L t U hU a
    simpa only [mul_inv_cancel_right] using X.mul_mem hga (X.inv_mem ha)
  refine ⟨hm',hn,t,ht,z,hz,hzc,hcommon,U,hU,hUV,hV,hVQ,hVc,hUc,hker,
    hVe,hVi,htU,htkill,hzne,htrans,?_,?_⟩
  · intro v hv hv1 g hg
    apply htrans v hv hv1 g
    have he : g*v*g⁻¹ = v :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)
    rw [he]
    exact hVmap hv
  · intro P hP hPne g hg
    obtain ⟨v,hv,hv1⟩ := P.bot_or_exists_ne_one.resolve_left hPne
    exact htrans v (hP hv) hv1 g
      (hVmap (hP ((mem_normalizer_iff.mp hg v).mp hv)))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
