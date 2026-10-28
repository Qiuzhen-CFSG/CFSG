module
public import Theory.GroupTheory.ClassTwoCommutator
public import Theory.Frattini.Intersection
public import Theory.Frattini.SquareImage
/-! # Frattini crossing-plane commutation
The source rows in the two marked rank-two quotients have the same order.
Their full preimages force the core factor to centralize a crossing plane;
disjoint core factors then contradict the nontrivial Frattini layer.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Stellmacher
variable {G:Type*} [Group G] [Finite G]
/-- Full commutator rows force the central factor to centralize the crossing plane. -/
theorem central_factor_centralizes_crossing
    (V W C:Subgroup G) [C.Normal] (q:ℕ)
    (hn:¬W≤centralizer (V:Set G))
    (hrow:∀w∈W,Nat.card (⁅(⊤:Subgroup G),zpowers w⁆:Subgroup G)≤q)
    (hgeom:∀w∈W,w∉centralizer (V:Set G)→
      q≤Nat.card (⁅V,zpowers w⁆:Subgroup G) ∧ Disjoint (⁅V,zpowers w⁆:Subgroup G) C) :
    W≤centralizer (C:Set G) := by
  have hreg (w:G) (hw:w∈W) (hv:w∉centralizer (V:Set G)) : w∈centralizer (C:Set G) := by
    obtain ⟨hq,hd⟩:=hgeom w hw hv
    have he:⁅V,zpowers w⁆=⁅(⊤:Subgroup G),zpowers w⁆:=
      eq_of_le_of_card_ge (commutator_mono le_top le_rfl) ((hrow w hw).trans hq)
    have hz:⁅C,zpowers w⁆=⊥:=by
      apply bot_unique
      exact (le_inf (he ▸ commutator_mono le_top le_rfl) (commutator_le_left _ _)).trans hd.le_bot
    intro c hc
    have hh:⁅c,w⁆∈⁅C,zpowers w⁆:=commutator_mem_commutator hc (mem_zpowers w)
    rw [hz,mem_bot] at hh
    exact commutatorElement_eq_one_iff_mul_comm.mp hh
  obtain ⟨w0,hw0,hn0⟩:=SetLike.not_le_iff_exists.mp hn
  intro w hw
  by_cases hnw:w∈centralizer (V:Set G)
  · have hh:w*w0∉centralizer (V:Set G):=by
      intro hh
      exact hn0 ((centralizer (V:Set G)).mul_mem_cancel_left hnw |>.mp hh)
    have hm:=hreg (w*w0) (W.mul_mem hw hw0) hh
    have h0:=hreg w0 hw0 hn0
    exact (centralizer (C:Set G)).mul_mem_cancel_right h0 |>.mp hm
  · exact hreg w hw hnw

/-- The two marked Frattini bounds turn core centralization into plane commutation. -/
theorem crossing_commutes_of_frattini_bounds
    (V W C D:Subgroup G) [C.Normal] (hp:IsPGroup 2 G) (q:ℕ)
    (hCV:C≤centralizer (V:Set G)) (hne:frattini C≠⊥) (hd:Disjoint C D)
    (hrow:∀w∈W,Nat.card (⁅(⊤:Subgroup G),zpowers w⁆:Subgroup G)≤q)
    (hgeom:∀w∈W,w∉centralizer (V:Set G)→
      q≤Nat.card (⁅V,zpowers w⁆:Subgroup G) ∧ Disjoint (⁅V,zpowers w⁆:Subgroup G) C)
    (hphi:¬W≤centralizer (V:Set G)→
      (frattini (centralizer (((V⊔W:Subgroup G):Set G)))).map (centralizer ((V⊔W:Subgroup G):Set G)).subtype≤C⊓D) :
    W≤centralizer (V:Set G) := by
  by_contra hn
  have hW:=central_factor_centralizes_crossing V W C q hn hrow hgeom
  have hCD:C≤centralizer ((V⊔W:Subgroup G):Set G):=
    le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hCV) hW)
  have hφ:(frattini C).map C.subtype≤⊥:=
    (frattini_image_le_of_le hCD (hp.to_subgroup _)).trans ((hphi hn).trans hd.le_bot)
  apply hne
  apply bot_unique
  intro c hc
  exact Subtype.ext (mem_bot.mp (hφ (mem_map_of_mem C.subtype hc)))
/-- A centralizer with elementary marked image has Frattini image in the marked kernel. -/
theorem centralizer_frattini_le_kernel {Q:Type*} [Group Q]
    (f:G→*Q) (V W:Subgroup G) (P:Subgroup Q)
    (hVP:V.map f=P) (hself:centralizer (P:Set Q)≤P)
    (hlift:P.comap f≤centralizer (V:Set G))
    (hW:∀w∈W,w^2=1)
    (hcent:∀t:Q,t^2=1→t∉P→P⊓centralizer ({t}:Set Q)≤center Q)
    [IsElementaryAbelian 2 (center Q)]
    (hn:¬W≤centralizer (V:Set G)) :
    (frattini (centralizer ((V⊔W:Subgroup G):Set G))).map (centralizer ((V⊔W:Subgroup G):Set G)).subtype≤f.ker := by
  obtain ⟨w,hw,hnw⟩:=SetLike.not_le_iff_exists.mp hn
  have ht:f w∉P:=fun hh=>hnw (hlift hh)
  have htp:(f w)^2=1:=by rw [←map_pow,hW w hw,map_one]
  let D:=centralizer ((V⊔W:Subgroup G):Set G)
  have him (d:D):f (d:G)∈center Q:=by
    apply hcent (f w) htp ht
    constructor
    · apply hself
      rintro y hy
      rw [←hVP] at hy
      obtain ⟨v,hv,rfl⟩:=hy
      simpa only [map_mul] using congrArg f (d.property v (mem_sup_left hv))
    · apply mem_centralizer_singleton_iff.mpr
      simpa only [map_mul] using congrArg f (d.property w (mem_sup_right hw)).symm
  have hh:=Theory.GroupTheory.frattini_le_ker_of_square_image (f.comp D.subtype) (fun d=>by
    exact elemPow_eq_one_of_isElementaryAbelian (f (d:G)) (him d))
  rintro _ ⟨d,hd,rfl⟩
  exact hh hd

/-- The crossing contradiction uses the two actual marked quotient kernels. -/
theorem crossing_commutes_of_two_quotients {Q Q':Type*} [Group Q] [Group Q']
    (f:G→*Q) (g:G→*Q') (V W:Subgroup G) (P:Subgroup Q) (P':Subgroup Q')
    (hp:IsPGroup 2 G) (q:ℕ) (hne:frattini f.ker≠⊥) (hd:Disjoint f.ker g.ker)
    (hVP:V.map f=P) (hWP:W.map g=P')
    (hself:centralizer (P:Set Q)≤P) (hself':centralizer (P':Set Q')≤P')
    (hlift:P.comap f≤centralizer (V:Set G)) (hlift':P'.comap g≤centralizer (W:Set G))
    (hV:∀v∈V,v^2=1) (hW:∀w∈W,w^2=1)
    (hcent:∀t:Q,t^2=1→t∉P→P⊓centralizer ({t}:Set Q)≤center Q)
    (hcent':∀t:Q',t^2=1→t∉P'→P'⊓centralizer ({t}:Set Q')≤center Q')
    [IsElementaryAbelian 2 (center Q)] [IsElementaryAbelian 2 (center Q')]
    (hrow:∀w∈W,Nat.card (⁅(⊤:Subgroup G),zpowers w⁆:Subgroup G)≤q)
    (hgeom:∀w∈W,w∉centralizer (V:Set G)→
      q≤Nat.card (⁅V,zpowers w⁆:Subgroup G) ∧ Disjoint (⁅V,zpowers w⁆:Subgroup G) f.ker) :
    W≤centralizer (V:Set G) := by
  have hCV:f.ker≤centralizer (V:Set G):=by
    intro c hc
    apply hlift
    change f c∈P
    rw [show f c=1 from hc]
    exact P.one_mem
  refine crossing_commutes_of_frattini_bounds V W f.ker g.ker hp q hCV hne hd hrow hgeom ?_
  intro hn
  have hn':¬V≤centralizer (W:Set G):=fun hh=>hn (le_centralizer_iff.mp hh)
  have h1:=centralizer_frattini_le_kernel f V W P hVP hself hlift hW hcent hn
  have h2:=centralizer_frattini_le_kernel g W V P' hWP hself' hlift' hV hcent' hn'
  rw [sup_comm W V] at h2
  exact le_inf h1 h2

/-- One marked quotient and its actual automorphic conjugate suffice. -/
theorem automorphic_plane_commutes {Q:Type*} [Group Q]
    (f:G→*Q) (e:G≃*G) (V:Subgroup G) (P:Subgroup Q)
    (hp:IsPGroup 2 G) (q:ℕ) (hne:frattini f.ker≠⊥)
    (hd:Disjoint f.ker (f.ker.map e.toMonoidHom))
    (hVP:V.map f=P) (hself:centralizer (P:Set Q)≤P)
    (hlift:P.comap f≤centralizer (V:Set G)) (hV:∀v∈V,v^2=1)
    (hcent:∀t:Q,t^2=1→t∉P→P⊓centralizer ({t}:Set Q)≤center Q)
    [IsElementaryAbelian 2 (center Q)]
    (hrow:∀v∈V,Nat.card (⁅(⊤:Subgroup G),zpowers v⁆:Subgroup G)≤q)
    (hgeom:∀w:G,w^2=1→w∉centralizer (V:Set G)→
      q≤Nat.card (⁅V,zpowers w⁆:Subgroup G) ∧ Disjoint (⁅V,zpowers w⁆:Subgroup G) f.ker) :
    V.map e.toMonoidHom≤centralizer (V:Set G) := by
  let W:=V.map e.toMonoidHom
  let g:=f.comp e.symm.toMonoidHom
  have hg:g.ker=f.ker.map e.toMonoidHom:=by
    ext x
    rw [mem_map_equiv]
    rfl
  have hWP:W.map g=P:=by
    rw [Subgroup.map_map]
    have he:g.comp e.toMonoidHom=f:=by ext x;simp [g]
    rw [he,hVP]
  have hlift':P.comap g≤centralizer (W:Set G):=by
    intro a ha
    have hb:e.symm a∈centralizer (V:Set G):=hlift ha
    rintro _ ⟨v,hv,rfl⟩
    change e v * a = a * e v
    simpa only [map_mul,e.apply_symm_apply] using congrArg e (hb v hv)
  have hW:∀w∈W,w^2=1:=by
    rintro _ ⟨v,hv,rfl⟩
    rw [←map_pow,hV v hv,map_one]
  have hr:∀w∈W,Nat.card (⁅(⊤:Subgroup G),zpowers w⁆:Subgroup G)≤q:=by
    rintro _ ⟨v,hv,rfl⟩
    have he:(⁅(⊤:Subgroup G),zpowers v⁆:Subgroup G).map e.toMonoidHom=
        ⁅(⊤:Subgroup G),zpowers (e v)⁆:=by
      rw [map_commutator,Subgroup.map_top_of_surjective _ e.surjective,
        MonoidHom.map_zpowers]
      rfl
    change Nat.card (⁅(⊤:Subgroup G),zpowers (e v)⁆:Subgroup G)≤q
    rw [←he,card_map_of_injective e.injective]
    exact hrow v hv
  apply crossing_commutes_of_two_quotients f g V W P P hp q hne (hg.symm ▸ hd)
    hVP hWP hself hself hlift hlift' hV hW hcent hcent hr
  exact fun w hw hn=>hgeom w (hW w hw) hn
end Stellmacher
