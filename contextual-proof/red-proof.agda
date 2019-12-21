{-# OPTIONS --allow-unsolved-metas #-}
module red-proof where

open import rules public
open import lemmas public
open import logical-relations public

infixl 6 _⊚[≤ᵣ]_
postulate
  fp : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ γ₁ γ₂ Σ′ Σ₀} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂ → Γ , Σ₀ ⊢ e ⦂ τ , Σ → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧ → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰ⟦ Σ ⨰ Σ′ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧
  _⊚[≤ᵣ]_ : ∀ {m n p : ℝ} →
    m ≤ᵣ n → n ≤ᵣ p
    ---------------
    → m ≤ᵣ p
  _⊚[≤ε]_ : ∀ {𝓋₁ 𝓋₂ p₁ p₂} →
    [𝒟]| 𝓋₁ - 𝓋₂ |≤ p₁ → p₁ ≤ p₂
    ---------------
    → [𝒟]| 𝓋₁ - 𝓋₂ |≤ p₂

-- Theorem 1.1.2 (Fundamental Property / (Metric Preservation in Fuzz)).
fp₂ : ∀ {N} {Γ : Γ[ N ]} {ℾ e τ Σ Σ₀ γ₁ γ₂ Σ′} → ℾ ⊢ γ₁ → ℾ ⊢ γ₂
  → Γ , Σ₀ ⊢ₚ e ⦂ τ , Σ
  → ⟨ γ₁ , γ₂ ⟩∈𝒢⟦ Σ′ ː ℾ ⟧
  → ⟨ γ₁ ⊢ e , γ₂ ⊢ e ⟩∈ℰₚ⟦ [vec]⌉ Σ′ ⌈⸢ one ⸣ ⨰ Σ ː (Σ′ ⟨⟨ τ ⟩⟩) ⟧

-- PRIVACY FUNCTION APPLICATION
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`papp {Σ₁ = Σ₁} {Σ₂ = Σ₂} {τ₂ = τ₂} {p = p} e₁ e₂) r[γ₁,γ₂]
  v₁ v₂ ⊢v₁ ⊢v₂
  ⟨ ⊢`papp {γ = γ₁} {e′ = e′₁} {𝓋₁ = 𝓋₁} ⊢e₁₁ ⊢e₁₂ ⊢e₁₂′ , ⊢`papp {γ = γ₂} {e′ = e′₂} {𝓋₁ = 𝓋₂} ⊢e₂₁ ⊢e₂₂ ⊢e₂₂′ ⟩
  -- v r₁ r₂ ∈sup𝓋₁ ∈sup𝓋₂ pr₁ pr₂
  with fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (pƛ⦂ e′₁ ∥ γ₁) (pƛ⦂ e′₂ ∥ γ₂) (typeSafety e₁ ⊢e₁₁) (typeSafety e₁ ⊢e₂₁) ⟨ ⊢e₁₁ , ⊢e₂₁ ⟩
     | fp ⊢γ₁ ⊢γ₂ e₂ r[γ₁,γ₂] 𝓋₁ 𝓋₂ (typeSafety e₂ ⊢e₁₂) (typeSafety e₂ ⊢e₂₂) ⟨ ⊢e₁₂ , ⊢e₂₂ ⟩
... | IH₁ | IH₂ with typeSafety {Σ′ = Σ′} e₁ ⊢e₁₁ | typeSafety {Σ′ = Σ′} e₁ ⊢e₂₁ | L9 Σ₂ Σ′ τ₂ | IH₁
… | ⊢pλ {Γ = Γ₁} {τ₁ = τ₁₁} {τ₂ = τ₂₁} {p = px†₁} {p′ = p†₁} {Σ = Σ′₁} ⊢γ₁′ ⊢e₁ ε₁₁ ε₁₂ ε₁₃
  | ⊢pλ {Γ = Γ₂} {τ₁ = τ₁₂} {τ₂ = τ₂₂} {p = px†₂} {p′ = p†₂} {Σ = Σ′₂} ⊢γ₂′ ⊢e₂ ε₂₁ ε₂₂ ε₂₃
  | ZZ
  | ⟨∃ ↯ , ⟨ ⟨ ⟨ ⟨ ↯ , ↯ ⟩ , ↯ ⟩ , ↯ ⟩ , IH′ ⟩ ⟩
  rewrite ZZ
  with IH′ {v₁ = 𝓋₁} {v₂ = 𝓋₂} {ε₁ = (typeSafety e₂ ⊢e₁₂)} {ε₂ = (typeSafety e₂ ⊢e₂₂)} {s′ = Σ₂ ⨰ Σ′}
            {Σ₀ = Σ′} (L3′ ⊢γ₁′ ⊢γ₂′ r[γ₁,γ₂]) IH₂ v₁ v₂ ⊢v₁ ⊢v₂ ⟨ ⊢e₁₂′ ,  ⊢e₂₂′ ⟩
... | IH′′ rewrite lzero[⨰]< Σ′ >
    | L0-3 (([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₁) +[qty] ⟨ 0 ⟩)
    | L-distrib-vec [vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ Σ₁ [vec]⌉ Σ₂ ⌈⸢ p ⸣ =
      let n = (𝑒^ᴿ (p2r (((mapⱽ (λ x → ⌉ x ⌈⸢ ⟨ 1 ⟩ ⸣) Σ′ ⨰ Σ₁) +[qty] ⟨ 0 ⟩) +[qty] ((⌉ Σ₂ ⨰ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣) ×[qty] p))))
          p′ = (𝑒^ᴿ (p2r ((([vec]⌉ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ⨰ Σ₁) +[qty] ⟨ 0 ⟩) +[qty] (⌉ Σ₂ ⨰ Σ′ ⌈⸢ ⟨ 1 ⟩ ⸣ ×[qty] p))))
      in _⊚[≤ε]_  IH′′ ((LPAPP  {p = p} Σ₁ Σ₂ Σ′))

-- PRIVACY CASE LEFT-LEFT
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`pcase {Σ₁₁ = Σ₁₁} {Σ₁₂ = Σ₁₂} {Σ₂ = Σ₂} e₁ e₂ e₃ τε) r[γ₁,γ₂]
  𝓋₁ 𝓋₂ ⊢𝓋₁ ⊢𝓋₂
  ⟨ ⊢`pcase/l {𝓋₁ = 𝓋₁₁} re₁ re₂ , ⊢`pcase/l {𝓋₁ = 𝓋₁₂} re₃ re₄ ⟩ v r₁ r₂ ∈sup𝓋₁ ∈sup𝓋₂ pr₁ pr₂ with typeSafety {Σ′ = Σ′} e₁ re₁
    | typeSafety {Σ′ = Σ′} e₁ re₃
    | fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (inl 𝓋₁₁) (inl 𝓋₁₂) (typeSafety {Σ′ = Σ′} e₁ re₁) (typeSafety {Σ′ = Σ′} e₁ re₃) ⟨ re₁ , re₃ ⟩
... | ⊢inl ⊢v₁ | ⊢inl ⊢v₂ | IH₁ with fp₂ (⊢s ⊢v₁ ⊢γ₁) (⊢s ⊢v₂ ⊢γ₂) e₂
    ⟨∃ ⊢v₁ , ⟨∃ ⊢v₂ , ⟨ IH₁ , r[γ₁,γ₂] ⟩ ⟩ ⟩ 𝓋₁ 𝓋₂
    (typeSafety₂ e₂ re₂) (typeSafety₂ e₂ re₄) ⟨ re₂ , re₄ ⟩ v r₁ r₂ ∈sup𝓋₁ ∈sup𝓋₂ pr₁ pr₂
... | IH₂ rewrite L0-3 (Σ′ ⨰ Σ₁₁) = subsumption₂ IH₂

-- PRIVACY CASE LEFT-RIGHT
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′}
  ⊢γ₁ ⊢γ₂
  (⊢`pcase {Σ₁ = Σ₁} {Σ₁₁ = Σ₁₁} {Σ₁₂ = Σ₁₂} {Σ₂ = Σ₂} {Σ₃ = Σ₃} {p₂ = p₂} {p₃ = p₃} e₁ e₂ e₃ τε) r[γ₁,γ₂]
  𝓋₁ 𝓋₂ ⊢𝓋₁ ⊢𝓋₂
  ⟨ ⊢`pcase/l {𝓋₁ = 𝓋₁₁} re₁ re₂ , ⊢`pcase/r {𝓋₁ = 𝓋₁₂} re₃ re₄ ⟩
  v r₁ r₂
  ∈sup𝓋₁
  ∈sup𝓋₂
  pr₁ pr₂
  with  fp ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] (inl 𝓋₁₁) (inr 𝓋₁₂) (typeSafety {Σ′ = Σ′} e₁ re₁) (typeSafety {Σ′ = Σ′} e₁ re₃) ⟨ re₁ , re₃ ⟩
... | IH with typeSafety {Σ′ = Σ′} e₁ re₁ | typeSafety {Σ′ = Σ′} e₁ re₃
… | ⊢inl X
  | ⊢inr Y rewrite LdistribJoin p₂ p₃ Σ′ Σ₁ Σ₁₁ Σ₁₂ Σ₂ Σ₃
  | L∞Pres Σ₁ Σ′ IH
  | L∞add p₂ p₃ Σ′ Σ₁₁ Σ₁₂ Σ₂ Σ₃ = ∞UB (nz-support 𝓋₂ v r₂ ∈sup𝓋₂ pr₂)

-- analogous to the above cases
-- fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`pcase e₁ e₂ e₃ τε) r[γ₁,γ₂] v₁ v₂ r₁ r₂ ε₁ ε₂ ⟨ ⊢`pcase/r x π₃ , ⊢`pcase/l x₁ π₄ ⟩ pr₁ pr₂ = {!   !}
-- fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′} ⊢γ₁ ⊢γ₂ (⊢`pcase e₁ e₂ e₃ τε) r[γ₁,γ₂] v₁ v₂ r₁ r₂ ε₁ ε₂ ⟨ ⊢`pcase/r x π₃ , ⊢`pcase/r x₁ π₄ ⟩ pr₁ pr₂ = {!   !}

-- RETURN
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′}
  ⊢γ₁ ⊢γ₂
  (⊢`return {Σ = Σ} e) r[γ₁,γ₂]
  𝓋₁ 𝓋₂ ⊢𝓋₁ ⊢𝓋₂
  ⟨ ⊢`return {𝓋₁ = v₁} e₁⇓ , ⊢`return {𝓋₁ = v₂} e₂⇓ ⟩
  v r₁ r₂
  ∈sup𝓋₁
  ∈sup𝓋₂
  pr₁ pr₂
  with fp ⊢γ₁ ⊢γ₂ e r[γ₁,γ₂] v₁ v₂ (typeSafety {Σ′ = Σ′} e e₁⇓) (typeSafety {Σ′ = Σ′} e e₂⇓) ⟨ e₁⇓ , e₂⇓ ⟩
… | IH with truncDichotomy₁ Σ′ Σ
... | ʟ x rewrite x | Lexp0 | lunit[×][ℝ]< r₂ > = LEqConstTermsZeroDist x IH ∈sup𝓋₁ ∈sup𝓋₂ pr₁ pr₂
... | ʀ y rewrite y = ∞UB (nz-support 𝓋₂ v r₂ ∈sup𝓋₂ pr₂)


-- BIND
fp₂ {Σ₀ = Σ₀} {Σ′ = Σ′}
  ⊢γ₁ ⊢γ₂
  (⊢`bind {Σ₁ = Σ₁} {Σ₂ = Σ₂} e₁ e₂) r[γ₁,γ₂]
  𝓋₁ 𝓋₂ ⊢𝓋₁ ⊢𝓋₂
  ⟨ ⊢`bind {𝓋₁ = 𝓋₁₁} ε₁ F₁ , ⊢`bind {𝓋₁ = 𝓋₁₂} ε₂ F₂ ⟩  -- v r₁ r₂ ∈sup𝓋₁ ∈sup𝓋₂ pr₁ pr₂
  with typeSafety₂ {Σ′ = Σ′} e₁ ε₁ | typeSafety₂ {Σ′ = Σ′} e₁ ε₂
... | ⊢v₁′ | ⊢v₂′
  with fp₂ ⊢γ₁ ⊢γ₂ e₁ r[γ₁,γ₂] 𝓋₁₁ 𝓋₁₂ ⊢v₁′ ⊢v₂′ ⟨ ε₁ , ε₂ ⟩
... | IH₁
  with sequentialComposition Σ′ 𝓋₁₁ 𝓋₁₂ F₁ F₂ Σ₁ Σ₂
    IH₁ λ x s₁ s₂ ⊢x ⊢ᴰdπ₁₁ ⊢ᴰdπ₁₂
    → fp₂ (⊢s ⊢x ⊢γ₁) (⊢s ⊢x ⊢γ₂) e₂ _ (dπ₁ (F₁ x s₁)) (dπ₁ (F₂ x s₂)) ⊢ᴰdπ₁₁ ⊢ᴰdπ₁₂
    ⟨ (dπ₂ (F₁ x s₁)) , (dπ₂ (F₂ x s₂)) ⟩
... | sC = sC

fp₂ _ = {!   !}
